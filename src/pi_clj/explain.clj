(ns pi-clj.explain
  (:gen-class))

; PURPOSE:      Explanation and abduction in PI.

; ********************************************************
; EXPLAIN treats explanation as a species of problem solving.  A
; fact is explained by treating it as a goal to be reached.  A rule
; is explained by treating its conditions as starting points and its
; action as a goal.  In the first case, the explanandum is a list of messages;
; in the second, it is a rule name.
;
(defn explain (type context explanandum)
   (my_print '&quot;-----------------------------------------------&quot;)
   (my_print '&quot;explaining &quot; explanandum)
   (setq prob_name (newsym 'explanation_))
   (cond ( (equal type 'fact)            ; explaining facts
           (setq start_list context
                 goal_list explanandum   ; actually, list of explananda
           )
         )
         ( (equal type 'rule)             ; explaining a rule
           (setq start_list (union context
                                   (get explanandum 'conditions)
                            )
                 goal_list (get explanandum 'actions)
           )
           (put prob_name 'rules_to_explain
                (cons explanandum (get prob_name 'rules_to_explain))
           )
     ;     remove explanandum from active messages
           (setq active_messages (remove (remove (last (get 'explanandum 'actions))
                                                 (get 'explanandum 'actions)
                                          )
                                          active_messages
                                  )
           )
 
           (put prob_name 'rule_explanandum explanandum)
         )
         (t (my_print '&quot;explanation error.&quot;))
     )
    (make_problem prob_name start_list goal_list 'explanandum)
    (put prob_name 'explan_status 'explanation)
    (setq e_result (solve_problem prob_name))      ; solve the problem
    (cond ( e_result (my_print explanandum '&quot; explained.&quot;)
                     ; if any rule was explained by an abductive
                     ; generalization, invoke theory evaluation (theory.l).
                     (cond ( (get prob_name 'abduc_gens)
                             (store_all_explns (get prob_name 'abduc_gens)
                                               explanandum
                             )
                           )
                      )
          )
                             
		     
          (t (my_print '&quot;No explanation found for &quot; explanandum))
    )
)
; **************************************************
; STORE_ALL_EXPLNS notes what abductively generalized rules
; played a role in explaining a rule.
(defn store_all_explns (rule_list rul)
   (prog (ruls)
      (setq ruls rule_list)
      loop
      (cond ( (null ruls) (return rule_list)))
      (store_expln (car ruls) rul)
      (setq ruls (cdr ruls))
      (go loop)
   )
)
; **************************************************
; TRIG_ABDUCE is called by trig.l and triggers abduction
; to facts, both simple and existential.
(defn trig_abduce ()
   (mapcar 'abduce_condns
	   (remove nil
		   (find_abductions (get (car active_problems) 'goals)
				    active_rules
		   )
	   )
   )
)
; **************************************************
; ABDUCE_CONDNS turns the conditions of a potentially explanatory 
; rule into hypotheses (compare building of sub-goals in
; prob_spread.l).
; Given rule A,B,C --&gt; E, with E to be explained, A, B, and C are
; hypothesized.  
; Works on triple: (&lt;explanandum&gt; &lt;rule&gt;
; &lt;conditions&gt;).  Returns a list of names of hypotheses.
; &lt;&lt;Major flaw:  check for consistency of hyptotheses is 
;   purely syntactc; will not catch semantic inconsistencies
;   such as x is green and red.&gt;&gt;
(defn abduce_condns (triple)
   (prog (explanandum rule condns condn result abduc_type)
      (setq explanandum (car triple)
	    rule (second triple)
	    condns (third triple)
      )
      ; bind up variables:
      (mapcar 'delete_binding univ_vbls)   ; remove old variable bindings
      (bind (second (car (get rule 'actions))) (second explanandum) )
      ; if all the variables are bound, it is a simple abduction, otherwise,
      ; existential abduction will be required.  Existential variables are
      ; specified in begin.l
      (cond ( (all_bound_vbls condns)
	      (setq abduc_type 'Simple)
	    )
	    ( t (setq abduc_type 'Existential))
      )
      ; make sure that none of the proposed hypotheses would
      ; contradict what is already known (not projected)
      (cond ( (abd_contradict condns active_messages)
              (return nil)
            )
      )
      loop
      (cond ( (null condns) 
	      (return (record_dependencies result) )
	    )
      )
      (setq condn (car condns))
      ; do an abduction on each condition:
      (setq result
	    (cons (abduce_fact explanandum rule condn abduc_type)
		  result
	    )
      )
      (setq condns (cdr condns))
      (go loop)
   )
)
; *********************************************************
; ALL_BOUND_VBLS checks too see whether all variables used by
; conditions in a list are bound.  If not, it gives them a binding
; from exist_vbls.
(defn all_bound_vbls (mess_list)
   (prog (vbls result)
      (setq vbls (union_map 'second mess_list))
      (setq result t)
      loop
      (cond ( (null vbls) (return result)))
      (cond ( (null (get (car vbls) 'binding))  ; no binding
	      (setq result nil)
	      (put (car vbls) 'binding (car exist_vbls))
              (setq last_exist_vbl (car exist_vbls))
	      (setq exist_vbls (cdr exist_vbls))
	    )
      )
      (setq vbls (cdr vbls))
      (go loop)
   )
)
; ********************************************************
; ABD_CONTRADICT checks whether possible hypotheses would
; contradict what is already known on a message list.
(defn abd_contradict (condn_lst mess_list)
   (prog (condits condit1)
      (setq condits condn_lst)
      loop
      (cond ( (null condits) (return nil)))
      (setq condit1 (list (car (car condits))
                          (get_binding (second (car condits)))
                          (third (car condits))
                    )
      )
      (cond ( (mess_contra condit1 mess_list)
              (return t)
            )
      )
      (setq condits (cdr condits))
   )
)
;**********************************************************
; MESS_CONTRA determines whether a message 
; contradicts one on a message list, based on known, not
; projected values.
; Cf. mess_on in misc.l.
; Returns the message from the list that contradicts.
(defn mess_contra (mess mess_lst)
  (prog (m_list mess_1)
    (setq m_list mess_lst)
    loop
    (cond ( (null m_list) (return nil) ))
    (setq mess_1 (car m_list))
    (cond ( (and (equal (car mess) (car mess_1))
                 (equal (second mess) (second mess_1))
                 (truth_contra (third mess) (third mess_1))
            )
            (return mess_1)
          )
     )
     (setq m_list (cdr m_list))
     (go loop)
   )
)
; *******************************************************
; TRUTH_CONTRA looks for flatly contradictory values.
(defn truth_contra (val1 val2)
   (or (and (equal val1 'true)
            (equal val2 'false)
       )
       (and (equal val1 'false)
            (equal val2 'true)
       )
   )
)
; *******************************************************
; RECORD_DEPENDENCIES notes what hypotheses were abduced together.
(defn record_dependencies (hyp_list)
   (prog (hyps)
      (setq hyps (remove nil hyp_list))
      loop
      (cond ( (null hyps) (return hyp_list)))
      (put (car hyps) 'co_hypotheses
           (remove nil
         	   (union (remove (car hyps) hyp_list) 
		          (get (car hyps) 'co_hypotheses)
                   )
	   )
      )
      (setq hyps (cdr hyps))
      (go loop)
   )
)
; ************************************************************
; ABDUCE_FACT creates a new explanatory hypothesis.
; Returns name of hypothesis abduced.
(defn abduce_fact (explanandum rul condn abd_type)
   (let ( explanandum_name concln default_confidence)
   (setq default_confidence .3)
   (setq explanandum_name
	 (cond ( (fifth explanandum) (fifth explanandum)) ; already named
	       ( t (fifth (name_message explanandum 'explanandum)))
	 )
   )
   ; set up abduced message
   (setq concln (list (car condn)
		      (get_binding (second condn))
		      (project_truth_value (third condn))
		      default_confidence
		)
   )
   (setq new_mess (mess_on concln active_messages 'found))
   ; if hypothesis has already been formed, simply note
   ; the new explanandum.
   (cond ((not_abduced (list (car concln) (second concln) (third concln))
                      explanandum
                      rul
          )
          (cond ( (and new_mess
                 ; from chain_explain:
                      (not (equal (car new_mess) conc_to_explain_with))
                      (atom_begins (fifth new_mess) #\H) ; hypothesis
                  )
                 ; then note abduction made
                 (put rul 'abductions
                      (cons (list (list (car new_mess) (second new_mess) 
                                        (third new_mess)
                                  )
                                  explanandum
                             )				  
                             (get rul 'abductions)
                       )
                  )
                  (my_print '&quot;Supplementary abduction of &quot; new_mess) 
                  (my_print '&quot;    from &quot; explanandum '&quot; and &quot; rul) 
        	  (store_expln (fifth new_mess) explanandum_name);see theory.l
                  (fifth new_mess)   ;  return hyp-name.
                )
                ; otherwise, form new hypothesis:
	        ( t (make_hypothesis concln explanandum_name rul abd_type))
          )
         )
   )
   ) ; end let   
)
; **********************************************************
; MAKE_HYPOTHESIS forms a new hypothesis, noting what it explains.
; &lt;&lt;Careful:  sometimes by a hypothesis I means its name, sometimes
;             its message.&gt;&gt;
; Here hyp is a message.
(defn make_hypothesis (hyp explanandum rul abd_type)
   (setq hyp (name_message hyp 'hypothesis))
   (cond ( (atom explanandum) ; want message
           (setq explanandum (get explanandum 'message)) 
         )
   )
   (my_print abd_type  '&quot; abduction of &quot;  hyp)
   (my_print '&quot;    from &quot;  explanandum  '&quot; and &quot;  rul )
   ; updated messages:
   (setq active_messages (cons hyp active_messages))
   (setq active_concepts (cons (car hyp) active_concepts))
   (put (car hyp) 'activation 1)
   ; store instance:
   (put (car hyp) 'instances 
	(cons hyp (get (car hyp) 'instances))
   )
   (setq active_projections (cons (fifth hyp) active_projections))
   ; note abduction made
   (put rul 'abductions
        (cons (list (list (car hyp) (second hyp) (third hyp))
                    explanandum
              )
              (get rul 'abductions)
        )
   )
   (put (car active_problems) 'abductions
	(cons (list hyp explanandum)
	      (get (car active_problems) 'abductions)
	)
   )
   ; note what explains what:
   (cond ( (and explanandum (not (atom explanandum)))
           (store_expln (fifth hyp) (fifth explanandum))
         )
   )
   ; if explanation is chaining (see concepts.l), then
   ; add hypothesis to list of goals to be explained.
   (cond ( chain_explain_flag
           (put (car active_problems) 'goals
                (cons hyp (get (car active_problems) 'goals))
           )
           ; stop explaining if start reached:
           (if (eq (car hyp) conc_to_explain_with)
               (setq stop_problem t)
           )
         )
   )
   
   ; return name of hypothesis
   (fifth hyp) 
)
; ***********************************************************
; FIND_ABDUCTIONS starts with a list of facts to be explained and a
; list of rules, and returns a set of triples of the form:
; (&lt;explanandum&gt; &lt;explaining rule&gt; &lt;condn to abduce&gt;).
 
(defn find_abductions (explananda rule_list)
   (prog (expa result)
      (setq expa explananda)
      (setq result nil)
      loop
      (cond ( (null expa) (return result)))
      (setq result (union result
                          (find_explns (car expa) rule_list)
                   )
      )
      (setq expa (cdr expa))
      (go loop)
   )
)
; *********************************************************************
; FIND_EXPLNS searches a list of rules for ones that potentially
; explain some given fact.  It checks for rules whose action matches
; the fact, and whose conditions are not all matched by the
; active messages.   Cf. subgoal finding.
; Returns triple of form (&lt;explanandum&gt; &lt;rule&gt; &lt;condition-list&gt;).
; Note:  won't work for rules with multiple actions.
(defn find_explns (explanandum rule_list)
   (prog (ruls result rul)
     (setq ruls rule_list)
     (setq result nil)
     loop
     (cond ( (null ruls) (return result)) )
     (setq rul (car ruls))
;    action of rule matches explanandum:
     (cond ( (and (equal (caar (get rul 'actions))
                         (car explanandum)
                  )
                  (truth_compatible (car (get rul 'actions))
                                    explanandum
                  )
             )
             (setq result
                   (cons (list explanandum
                               rul
                               (get rul 'conditions)
                         )
                         result                       
                   )
              )
          )  
      )
      (setq ruls (cdr ruls))
      (go loop)
   )
)
; *********************************************************
;  &lt;&lt;OBSOLETE&gt;&gt;
;  ALL_BUT_ONE (rule) checks to see if all but one condition of the
;  rule is an active message.  if so, it returns that member.  the role of this
;  function in abduction is to find one condition of a potentially
;  explaining rule which is not on the message list; that condition is then
;  abduced.  this function returns a pair: (&lt;rule&gt; &lt;condition&gt;)
 
(defn all_but_one (rul)
   (prog (condns result count)
     (setq condns (get rul 'conditions)
           count  0
           result nil
     )
     loop
     (cond ( (greaterp count 1)       ; more than one
             (return nil)
           )
           ( (null condns)
             (return result)       ; 1 or none
           )
     )
     (cond ( (not (member (car condns) active_messages))
             (setq result (car condns))
             (setq count (add1 count))
           )
     )
     (setq condns (cdr condns))
     (go loop)
   )
)
; *********************************************************
; NOT_ABDUCED checks that an abduction has not already been made (refraction).
; Extra complication to prevent duplicate existential abductions. 
(defn not_abduced (hyp explanandum rul)
  (and
   (not_member (list hyp explanandum)
               (get rul 'abductions)
   )   
   ; kluge:  only one existential abduction per rule:
   (null (intersection all_exist_vbls
                       (union_map 'second_first (get rul 'abductions))
         )
   )
  )
)

; SECOND_FIRST takes the second element of the first element of a list.
(defn second_first (lst) (second (car lst)))
; *********************************************************
;        ABDUCTIVE GENERALIZATION
; *********************************************************
; TRIG_ABD_GEN is called by trigger in trig.l.  It looks 
; through the list of active messages for general hypotheses, e.g.
; H(x), that have played a role in explaining why G(x), given that 
; F(x).  It then forms the rule: Fx -&gt; Hx.  Forms rules with any number
; of conditions and can handle relations, too.
(defn trig_abd_gen ()
   (mapcar 'build_abd_gen (find_gen_hypoth active_messages))
)
; **************************************************************
; FIND_GEN_HYPOTH finds messages that are hypotheses using general variables.
(defn find_gen_hypoth (mess_lst)
    (prog (messages first_mess result)
       (setq messages mess_lst)
       (setq result nil)
       loop
       (cond ( (null messages) (return result)))
       (setq first_mess (car messages))
       (cond ( (and (fifth first_mess)
                    (atom first_mess)
                    (equal (get (fifth first_mess) 'data_type) 'hypothesis)
                    (contains_gen_vbl (second first_mess))
               )
               (setq result (cons first_mess result))
             )
       )
       (setq messages (cdr messages))
       (go loop)
   )
)
; ****************************************************************
; CONTAINS_GEN_VBL determines whether a list of arguments contains at
; least one universal variable $x.
(defn contains_gen_vbl (arg_lst)
    (cond ( (null arg_lst) nil)
          ( (atom_begins (car arg_lst) #\$) t)
          ( t (contains_gen_vbl (cdr arg_lst)))
    )
)
; ******************************************************************
; BUILD_ABD_GEN forms a general rule from the general hypothesis, looking
; for starting conditions with the same variables as the hypothesis.
; global variable:  abd_rule_made
(defn build_abd_gen (hyp_mess)
    (cond ( (null (member hyp_mess 
                          (get (car active_problems) 'abduc_gens)
                  )
            )
            (setq abd_rule_made
                  (make_rule_long (car hyp_mess)
                                  (mess_with_vbl (second hyp_mess) 
                                                 (get (car active_problems)
                                                      'start
                                                 )
                                  )
                                  (list (list (car hyp_mess)
                                              (second hyp_mess) 
                                              (un_project_truth_val (third hyp_mess))
                                              'deduce
                                        )
                                  )
                                  (car hyp_mess)  ; where to get slot?
                                  'default
                                  .1
                   )
            )
         )
    )
    (cond ( abd_rule_made     
            (my_print '&quot;Abductive generalization formed from &quot; hyp_mess)
            (put (car active_problems) 'abduc_gens 
                 (cons abd_rule_made
                       (get (car active_problems) 'abduc_gens)
                 )
            )
            (put (car all_rules) 'how_formed 'abduced)     
          )
    )
)
; ********************************************************************
; MESS_WITH_VBL returns those messages that have some of a set of arguments
; in common with a given argument list.
(defn mess_with_vbl (arg_lst mess_lst)
    (prog (messages first_mess result)
       (setq messages mess_lst)
       (setq result nil)
       loop
       (cond ( (null messages) (return result)))
       (setq first_mess (car messages))
       (cond ( (contains_gen_vbl (intersect arg_lst
                                             (second first_mess)
                                  )
               )
               (setq result (cons first_mess result))
             )
       )
       (setq messages (cdr messages))
       (go loop)
    )
)
; *****************************************************
; UN_PROJECT_TRUTH_VAL turns a 
; truth value into one with the 'proj' stripped off.
(defn un_project_truth_val (val)
    (if (equal val 'proj_true) 'true 'false)
)

; For ANALOGICAL ABDUCTION, see analog.l.