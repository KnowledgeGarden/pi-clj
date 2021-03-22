(ns pi-clj.motiv
  (:gen-class))

; PURPOSE:     motivated inference

; See Thagard and Kunda, &quot;Hot Cognition&quot;, Proc. Cog. Sci. Soc. 1987.
; This file contains functions for constructing a representation of the
; self and using it to motivate inferences, shifting both deduction
; and induction in directions determined by the motives of the self.
; ********************************************************************
;                Representation of the self.
; ---------------------------------------------------------------------
; MAKE_SELF sets up the self data structure, which has the following 
; properties:
;         name:
;         data_type:   self
;         attributes:  list of attribute, each with:
;                                       message:
;                                       importance:
;                                       activation:
;                                           
;         motives:     list of motive, each with:
;                                 message
;                                 activation
;                                 priority
;                                 
;
;
; In the following definition, attributes is a list consisting of 
; lists with the structure:  (attribute activation message importance).
; And motives is a list with the structure:
;    (motive activation message priority)
;
(defn make_self (self_name attributes motives)
   (put self_name 'data_type 'self)
   (put self_name 'attributes attributes)
   (put self_name 'motives motives)
   (make_concept_s (attributes_of self_name))
   (make_concept_s (motives_of self_name))
)
; ****************************************************************
;   Data abstraction of self.
; ****************************************************************
; ATTRIBUTES_OF
(defn attributes_of (self)
   (mapcar 'car (get self 'attributes))
)
; MOTIVES_OF
(defn motives_of (self)
   (mapcar 'car (get self 'motives))
)
; ATTRIB_ACTIVN_OF
(defn attrib_activn_of (self attrib)
   (second (assoc attrib (get self 'attributes)))
)
; ATTRIB_MESS_OF
(defn attrib_mess_of (self attrib)
   (third (assoc attrib (get self 'attributes)))
)
; ATTRIB_MESSAGES_OF 
(defn attrib_messages_of (self)
   (third_s (get self 'attributes))
)
; 
; ATTRIB_IMPORT_OF
(defn attrib_import_of (self attrib)
   (fourth (assoc attrib (get self 'attributes)))
)
; MOTIV_MESS_OF
(defn motiv_mess_of (self motiv)
    (third (assoc motiv (get self 'motives)))
)
; MOTIV_MESSAGES_OF
(defn motiv_messages_of (self)
    (third_s (get self 'motives))
)
; MOTIV_ACTIVN_OF
(defn motiv_activn_of (self motiv)
   (second (assoc motiv (get self 'motives)))
)
; MOTIV_PRIOR_OF
(defn motiv_prior_of (self motiv)
    (fourth (assoc motiv (get self 'motives)))
)
; THIRD_S returns a list of all the third elements of items in a list.
(defn third_s (lst)
   (mapcar 'third lst)
)
; NAME_FROM_GOAL
(defn name_from_goal (goal_mess)
   (fifth goal_mess)
)
; *********************************************************************
; PRINT_SELF prints out a self and
; associated attributes and motives.
(defn print_self (self)
   (my_print '&quot;Self: &quot; self)
   (my_print '&quot;   Attributes: &quot;)
   (mapcar 'print_attrib (get self 'attributes))
   (my_print '&quot;   Motives: &quot;)
   (mapcar 'print_motiv (get self 'motives))
)
; **********************************************************
; PRINT_ATTRIB prints out attribute.
(defn print_attrib (attr_lst)
   (my_print '&quot;      Attribute: &quot; (car attr_lst))
   (my_print '&quot;         Activation: &quot; (second attr_lst))
   (my_print '&quot;         Message: &quot; (third attr_lst))
   (my_print '&quot;         Importance:  &quot; (fourth attr_lst))
   
)
; **********************************************************
; PRINT_MOTIV prints out motive.
(defn print_motiv (mot_lst)
   (my_print '&quot;      Motive: &quot; (car mot_lst))
   (my_print '&quot;         Activation: &quot; (second mot_lst))
   (my_print '&quot;         Message: &quot; (third mot_lst))
   (my_print '&quot;         Priority: &quot; (fourth mot_lst))
)
; ****************************************************************
;         Determining the relevance of a conclusion to the self.
; ***************************************************************
; MOTIVE_RELEVANCE determines the relevance of a possible conclusion to
; a self.  Returns 0 if conclusion is 
; irrelevant, between -1 and 0 if it goes against
; accomplishing a goal, and between 0 and 1 if it contributes to a goal.
(defn motive_relevance (self message)
   (prog (motivs)
      (my_print '&quot;What is relevance of &quot; message '&quot; to &quot; self '&quot;?&quot;)
      (setq motivs (rel_motives self message))
      (setq result 0)
      loop
      (cond ( (null motivs) 
              (my_print '&quot;Overall relevance of &quot; message '&quot; to &quot;
                        self '&quot; is:  &quot; result
              )
              (return result)
            )
      )
      (setq result (add result (motiv_value self (car motivs) message)))
      (setq motivs (cdr motivs))
      (go loop)
   )
)
; ************************************************************
; REL_MOTIVES finds what motives are relevant to a given conclusion.
; This does a deductive search using the problem solver from prob.l.
; If A is a message
; and there are rules A -&gt; B, B -&gt;C, and C -&gt; M, where M is a motive,
; then A is relevant to M. Relevance can be positive or negative,
; depending on truth values: it's good if you want something to be
; true and it is.
(defn rel_motives (self mess)
   (let ( (goal_sat_messages nil)
          (motiv_projn nil)
          (prob_name (newsym 'motiv_rel_prob_))
        )
        (setq rel_motiv_flag t)
        (start_projection (car mess))
        (setq motiv_projn (car active_projections))
        (make_problem prob_name
                      ; start with projected conclusion and 
                      ;    the attributes of self:
                      (append (list (list (car mess)
                                          (second mess)
                                          (project_truth_value (third mess))
                                          1
                                          (list (car active_projections))
                                     )
                               )
                              (attrib_messages_of self)
                      )
                      (motiv_messages_of self)  ; goals are self's motives
                      'motive_relevance
        )
        ; solve the problem:
        (setq motive_relevance_flag t)
        (solve_problem prob_name)
        (setq active_projections (remove motiv_projn active_projections))
        ; calculate what motives are accomplished:
        (setq goal_sat_messages 
              (motives_accomplished mess (get prob_name 'goals) active_messages)
        )
        (cond ( goal_sat_messages 
                (my_print '&quot;Motives of self &quot;  self '&quot; relevant to &quot;
                          mess '&quot; are: &quot;  goal_sat_messages
                )
                (put (car mess) 'relevant_motives  ; store for rationalise
                   (cons (list self (concepts_from goal_sat_messages))
                           (get (car mess) 'relevant_motives)
                     )
                )  
                goal_sat_messages
              )
              ( t (my_print mess '&quot; is irrelevant to &quot; self)
                  nil
              )
        )
        (setq rel_motiv_flag nil)
        goal_sat_messages  ; returned
   )
)
; ***************************************************************
; MOTIVES_ACCOMPLISHED is like accomplished in prob.l, except that
; it checks all motives to see if they are satisfed, as well as
; for counter-satisfied motives.
(defn motives_accomplished (mess goal_list mess_list)
  (prog (lst result goal)
        (setq lst goal_list )
        loop
        (setq goal (car lst))
        (cond ( (null lst) (return result) ) )
        (cond ( (is_satisfied goal mess_list)
                (setq result (cons goal result))
 	        (put (name_from_goal goal) 'relevant_messages
                     (cons (list mess 1)
                           (get (name_from_goal goal) 'relevant_messages)
                     )
                )
              )
              (t (cond ( (counter_satisfied goal mess_list)
                         (setq result (cons goal result))
                         (put (name_from_goal goal) 'relevant_messages
                              (cons (list mess -1)
                                    (get (name_from_goal goal) 
                                         'relevant_messages
                                    )
                              )
                         )
                       )
                  )
               )
           )
        (setq lst (cdr lst) )
        (go loop)
   )
)
; ******************************************************
; COUNTER_SATISFIED notes cases where an inferred message runs counter
; to desired goals.
(defn counter_satisfied (goal mess_list)
  (prog (lst mess)
        (setq lst mess_list)
        loop
        (setq mess (car lst))
        (cond ( (null lst) (return nil) ) )
        (cond ( (and (equal (car goal) (car mess))
                     (arg_equal (second goal) (second mess))
                     (not (truth_compatible goal mess))
                )
                (return t)
              )
        )
        (setq lst (cdr lst) )
        (go loop)
   )
  
)
; **************************************************
; MOTIV_VALUE calculates the current value of a motive, taking
; into account both its priority and degree of motivation.
(defn motiv_value (self motive_mess message)
   (times (motiv_activn_of self (car motive_mess))
          (motiv_prior_of self (car motive_mess))
          (motive_direction motive_mess message)  ; set up by functions above
   )
)  
; *****************************************************
; MOTIVE_DIRECTION indicates whether a message has been found to be
; positively or negative relevant.
; Note: to get a probability of accomplishment of a goal, use the
; confidence of the message (later).
(defn motive_direction (mot_mess mess)
   (second (assoc mess
                  (get (name_from_goal mot_mess) 'relevant_messages)
           )
   )
)
; ***************************************************
;    MOTIVATED INFERENCE
; ***************************************************
; MOTIV_GEN does motivated generalizations.
; If a rule turns out to be positively relevant to the
; self, a lower threshold for inference is set.
; If it is negatively relevant, a higher threshold is
; set. 
(defn motiv_gen (self class property)
   ; announce
   (my_print '&quot;**********************************************&quot;)
   (my_print '&quot;Motivated generalization by &quot; self '&quot;:  &quot;
              class '&quot; -&gt; &quot; property '&quot; ?&quot; 
   )
   (let ( (relevance (motive_relevance self ;
                                       (list property (list self) 'true)
                     ) ; relevance of self being B.
          )
          (basic_threshold gen_threshold)   ; for gen_threshold see gen.l
          (gen_done? nil)
        )
         
        ; if being B is good, try to show that S is A and that A-&gt;B:
        
        (cond ( (&gt; relevance 0)
                ; try to show that S is A:          
                (cond ( (search_mess self 
                                     (make_self_message self class 'true)
                                     relevance
                        )
                     
                        ; if S is A, try to show that A's are B's
                        (search_instances self 
                                          (make_self_message self class 'true)
                                          (make_self_message self property 'true)
                                          relevance
                        )
                        ; and lower threshold
                        (setq gen_threshold (diff gen_threshold .2))
                      )
                 )
              )
        )
        ; if being B is bad:
        (cond ( (&lt; relevance 0)                       
                ; try to show that self is not A:
                (cond ( (and (not (search_mess self
                                           (make_self_message self 
                                                              class 
                                                              'false
                                           )
                                           relevance  
                                   )
                                   
                              )
                              ; self is A
                              (is_self? self class)
                        )
                        ; try to find A's that are not B's
                        (search_instances self
                                          (make_self_message self class 'true)
                                          (make_self_message self property 'false)
                                          relevance
                        )
                        ; and set threshold high
                        (setq gen_threshold (+ gen_threshold .2)) 
                      )
                  )
          )
        )
        (my_print '&quot;Generalization threshold is now: &quot; gen_threshold)
        (my_print '&quot;Number of instances needed for generalization is: &quot;
                  (times gen_threshold max_instances)
        )
        ; now generalize as before.
        (setq gen_done? (generalize (list class property nil)))  ; see gen.l
        ; if generalizing occurred despite negative relevance, adjust self.
       
        (cond ( (and gen_done? (&lt; relevance 0))
                (rationalise self property)
              )
        )
        ; set back gen_threshold
        (setq gen_threshold basic_threshold)
   )
)
; **************************************************
; MAKE_SELF_MESSAGE sets up a message involving the self:
(defn make_self_message (self predicate truth_val)
   (list predicate (list self) truth_val)
)
; ***************************************************
; IS_SELF? determines whether a concept applies to a self.
(defn is_self? (self conc)
   (or (member conc (attributes_of self))
       (is? self conc)
       (memberlist (make_self_message self conc 'true)
                   (get conc 'instances)
       )
   )
)
; ***************************************************
; MOTIVE_RELEVANCE_OF_RULE calculates the potential motivation of a
; potential rule, which is 0 if the condition does not apply to the self,
; and the motive relevance of the action otherwise.
; For now this only works with simple rules if A then B.
; Not now used in above.
(defn motive_relevance_of_rule (self class property)
    (cond ( (attribute_relevant? self 
                                 (list class (list self) 'true)
            )
            (motive_relevance self 
                              (list property (list self) 'true)
            )
          )
          (t 0)
    )
)
; **********************************************************
; ATTRIBUTE_RELEVANT? checks to see if a message is relevant to
; the self.
(defn attribute_relevant? (self mess)
   (cond ( (mess_on mess (attrib_messages_of self) 'sought)
           (my_print '&quot;Attribute &quot; mess '&quot; does apply to &quot; self)
           t
         )
         (t (my_print '&quot;Attribute &quot; mess '&quot; does not apply to &quot; self)
            nil
         )
   )
)
; ***************************************************
; SELF_INSTANTIATE plugs a self into the argument in a message.
(defn self_instantiate (self mess)
   (subst (second mess) (list self) mess)
)
; ***************************************************
; RATIONALISE overcomes a negative generalization about the
; self by adjusting the self's motivations.  (Attributes cannot
; be further adjusted because a search already failed to show
; that a self lacked the relevant attribute.)  This function
; figures out what motives were negatively affected by an attribute
; that generalization would infer the self to have, and therefore
; downplay the importance of such motives.
; This is a bit too simple, since it should select out which motives
; were part of the negative evaluation.
(defn rationalise (self attrib)
   (prog (motives)
      (setq motives (second (assoc self (get attrib 'relevant_motives))))
      (my_print '&quot;Rationalization  by &quot; self
                '&quot; through  reduction of priority of motives &quot;
                motives
      )
      loop
      (if (null motives) (return '&quot;Rationalizing done.&quot;))
      (reduce_priority self (car motives))
      (setq motives (cdr motives))
      (go loop)
   )
)
; ***************************************************
; REDUCE_PRIORITY lowers the priority of a self's motive.
(defn reduce_priority (self motive)
   (let ( (old_mot (assoc motive (get self 'motives)))
        )
        (my_print '&quot;OLD &quot; old_mot)
        (put self 'motives
             (cons (list motive (second old_mot) (third old_mot)
                         (/ (fourth old_mot) motiv_redn)
                   )
                   (remove old_mot (get self 'motives) :test 'equal)
             )
        )
        (my_print '&quot;Priority of motive &quot; motive '&quot; of &quot; self
                  '&quot; reduced to &quot; (motiv_prior_of self motive)
        )
   )
)
; ***************************************************
; REMOVE_ATTRIB/MOTIV deletes an attribute
; or motive from a self.
(defn remove_attrib/motiv (self attr kind)
   (put self kind
        (remove (assoc attr
                       (get self kind)
                )
                (get self kind)
        )
   )
)
;*************************************************************
;                  Motivated searches
; ************************************************************
; SEARCH_MESS  does a search through memory to try to show
; that a message holds.  Urgency is the degree of importance
; determined by motive_relevance:  the greater the urgency,
; the deeper the search, i.e. the more timesteps allowed.
(defn search_mess (self mess urgency)
   (let ( (prob (newsym 'search_mess))
           (old_time timesteps)
           (result nil)
        )
        (my_print '&quot;Attempting to show &quot; mess)
        (init_prob)
        (setq timesteps (urgency_to_time urgency))
        (make_problem prob
                      (attrib_messages_of self)
                      (list mess)
                      'search_mess
         )
         (setq result  (solve_problem prob))
         (setq timesteps old_time)
         (if result (my_print '&quot;Search showed: &quot; mess)
                    ; else
                    (my_print '&quot;Search failed: &quot; mess)
         )
         result
   )
)
; ****************************************************************
; URGENCY_TO_TIME translates the urgency of an inference into 
; the number of timesteps a problem should run.
(defn urgency_to_time (urg)
   (min 10 (round urg))
)
; *****************************************************************
; SEARCH_INSTANCES looks for instances messages.
; It sets up a problem to find things that are A and B,
; or A and -B.
; It does not actually return the found instances, but the 
; results of its inferences are stored with A and B for use
; in checking for counterexamples and 
; in calculating the number of instances:  see gen.l.

(defn search_instances (self mess1 mess2 urgency)
   (let ( (prob (newsym 'search_instances))
           (old_time timesteps)
           (result nil)
        )
        (my_print '&quot;Searching for instances of &quot; mess1 '&quot; and &quot; mess2)
        (my_print '&quot;Known instances of &quot; (car mess1) '&quot; before search: &quot; 
                  (get (car mess1) 'instances)
        )
        (my_print '&quot;Known instances of &quot; (car mess2) '&quot; before search: &quot; 
                  (get (car mess2) 'instances)
        )
        (init_prob)
        (setq timesteps (urgency_to_time urgency))
        (make_problem prob
                      nil
                      (list mess1 mess2)
                      'search_instances
         )
         (setq result  (solve_problem prob))
         (setq timesteps old_time)
         (my_print '&quot;Known instances of &quot; (car mess1)
                   '&quot; after search: &quot; (get (car mess1) 'instances)
         )
         (my_print '&quot;Known instances of &quot; (car mess2)
                   '&quot; after search: &quot; (get (car mess2) 'instances)
         )
   )
)
; ****************************************************************       
; MAKE_SEARCH_MESS  constructs a message that will never actually
; be matched fully, but which will help to direct subgoaling.
                       
(defn make_search_mess (conc)
   (list conc (no_arg) 'true)
)



; ***************************************************
;       DECISION MAKING
; ***************************************************
; DECIDE is a function for deciding which of a set of actions to
; perform.  Deciding is (normatively) motivated inference:  choose
; what action best accomplishes your goals.
; Acts are atoms with the following properties:
;    Acts
;        data-type:    acts
;        description:  message
;        value:        number calculated by motive_relevance.
(defn decide (self list_of_acts)
   (prog (acts best_act)
      (setq acts list_of_acts)
      (cond ( (null acts) 
              (setq best_act (highest list_of_acts value))
              (my_print '&quot;Decision:  &quot;  best_act '&quot; is the best act.&quot;)
              best_act
            )
      )
      loop
      (set_decision_value self (car lst))
      (setq acts (cdr acts))
      (go loop)
   )
)
; ***********************************************************
; SET_DECISION_VALUE calculates the value of an act relative to the
; agents motives.  A better version would also take into account
; probabilites.
(defn set_decision_value (self act)
   (put act 'value
        (motive_relevance self (get act 'description))
   )
)
; ************************************************************
; end of motiv.l.
;  FILE:        prob.l
;  PURPOSE:     Problem solving, part of PI
;  PROGRAMMER:  Paul Thagard
;  CREATED:     5-24-84
;  UPDATED:     10-30-86
;  Note:  functions 13-24 in prob_fire
;         functions 25-   in prob_spread
; ******************************************************************** 0
; INIT_PROB sets everything up to start a problem clean
   
(defn init_prob ()
   (mapcar 'de_activate active_concepts)
   (mapcar 'un_refract all_rules)     ; cancel refractions 
   (setq   all_goal        nil
           all_hypothesis  nil
           all_explanandum nil
 
           active_projections nil
           active_concepts  nil
           active_messages  nil
           active_rules     nil
           active_solutions nil
           active_problems  nil
           all_projections  nil
           
           stop_problem nil
           known_messages   nil
           projected_messages nil
   )

)
 
(defn de_activate (struc)
   (put struc 'activation 0)
   (put struc 'forward_activated_by nil)
   (put struc 'goal_activated_by nil)
)
;*************************************************************************** 1
;  SOLVE_PROBLEM (prob_name) attempts to solve the given problem.
 
(defn solve_problem (prob_name)
   (declare (special best_rules))
   (cond (  trace_prob
            (my_print '&quot;------------------------------------------&quot;)
            (my_print  '&quot;SOLVING PROBLEM:  &quot; prob_name )
            (my_print  '&quot;STARTING FROM:  &quot;   (get prob_name 'start))
            (my_print  '&quot;GOALS:  &quot;  (get prob_name 'goals) )
         )
   )
   ;initializations:
   (setq active_problems    (cons prob_name active_problems))
   (put prob_name 'rules_used nil)         ; rules used in solution
   (put prob_name 'rules_sub_goaled nil)   ; rules furnishing subgoals
   (put prob_name 'concepts_used nil)      ; concepts used in solution
   (put prob_name 'effects nil)            ; effectors used in solution
   (put prob_name 'effects_objs nil)
   (setq activated_last_time nil)
   (unless rel_motiv_flag
           (setq active_projections nil)
   )
     
;  add starting conditions to active messages
   (setq active_messages (union active_messages
                                (get prob_name 'start)
                         )
   )
;  add goals (want-trues) for non-explanation problems:
   (cond ( (not_equal (get prob_name 'explan_status) 'explanation)
           (setq active_messages (union active_messages
                                        (get prob_name 'goals)
                                 )
           )
         )
   )
   
;  store starting conditions with relevant concepts
   (mapcar '(lambda (mess)
              (put (car mess) 'instances
                   (cons mess
                         (get (car mess) 'instances)
                    )
               )
            )
            ; store goals if not explanation problem
            (cond ( (equal 'explanation (get prob_name 'explan_status))
                    (get prob_name 'start)
                  )
                  (t (union (get prob_name 'goals)
                            (get prob_name 'start)
                     )
                  )
            )
   )
;  make concepts from start and goal active
   (setq active_concepts (union_list active_concepts
                                     (concepts_from (get prob_name 'start))
                                     (concepts_from (get prob_name 'goals))
                         )
   )
   (setq just_activated active_concepts)  ; for activ_ordinates in prob_spread
   (mapcar '(lambda (cpt)
                (put cpt 'activation 1)
            )
            active_concepts             ;  fix: make proportional to 
                                        ;  importance of goals.
   )
; ^^^^^^^^^^^^^ MAIN LOOP ^^^^^^^^^^^^^^^^^^^^^^^^
;  begin main loop
   (prog (clock)
         (setq clock 0)
         loop
         (setq clock (add1 clock))
         (cond ( trace_prob
                 (pi_status prob_name clock)  ; print system status
               )
         )
         (cond ( debug (dump_system)))    ; dump all system info.
;        (observe )  ; get input from environment - not yet implemented
  
;        (my_print '&quot;DEBUG active_messages: &quot; active_messages)
         (cond ( trig_flag (trigger))) ;trigger induction - see trig.l
         (cond ( (check_for_success prob_name)  ; problem done?
;                if so, store all rules from active projections 
;                and store problem solution with concepts: see store.l
                 (store_problem prob_name)
                
;                reward the rules which started good projections:
                 ;TEMP(reward (projecting_rules prob_name))
;                generalize rules for goal achievement: see gen.l
                 ;TEMP(gen_goal (projecting_rules prob_name))
;                if an analogy was used, form an analogical schema
                 (cond ( (get prob_name 'analogies_used)
                         (schem_all prob_name (get prob_name 'analogies_used))
                       ) ; see ana_schem.l
                 )
                 (setq best_rules nil)   
                 (my_print (car active_problems) '&quot; solved.&quot;)
                 ;(cond ( print_to_file (princ '&quot;Problem solved.&quot;)))
                 (return t)
               )
         )
 


         (cond ( (or (equal clock timesteps)
                     (and ; (null analogy_flag)
                          (&gt; clock 2) 
                          (null best_rules)      ; nothing fired at last step
                          (null just_activated)  ; no new concepts activated
                          (null activated_last_time)
                          (null goal_activated)
                     )
                 )                          ; see prob_fire.l.
                 (my_print '&quot;Solution failed for &quot; (car active_problems))
                 (my_print '&quot;---------------------------------------------&quot;)
                 (return nil)                          ; time limit
               )
         )

         ; look for analogous problems, after de-activating an analogous
         ; solution that hasn't led anywhere:
         (cond ( (and (greaterp clock 2)
                      (null best_rules)  ; no rules fired on last step.
                      (null activated_last_time)
                 )
                 (put prob_name 'bad_ana_problems    ; see prob_spread.l
                      (cons (highest active_solutions 'activation)
                            (get prob_name 'bad_ana_problems)
                      )
                 )
               )
         )
         ; analogical problem solving:
         (cond ( analogy_flag  (trig_analog prob_name active_solutions)))
         (cond ( go_backwards (set_sub_goals)) )
 
         (fire_rules  )                   ; fire selected rules
         (change_activation )             ; adjust activation of
                                          ;    concepts, rules, messages
         
         (go loop)
   )  ; end prog
;  add:   alter active_problems and active_projections
)
;  end of solve_problem
; ***************************************************************** 1
; PROJECTING_RULES gives a list of those rules that started
; projections.
(defn projecting_rules (prob_nam)
    (declare (special prob_nam))
    (mapcar '(lambda (proj)
                (last (get prob_nam proj))
             )
             active_projections
    )
)
;********************************************************************** 2
;  projections are started by store_actions and stopped by
;  check_for_success.  see those functions below.
;  START_PROJECTION starts a projection.
 
(defn start_projection (effector)
   (setq proj_name (newsym 'proj_))
   (put proj_name 'first_effector effector)
   (setq active_projections (cons proj_name active_projections))
    
   (cond ( trace_prob
           (my_print  '&quot;Starting projection &quot; proj_name
                      '&quot; from &quot; effector
           )
           ;(my_print '&quot;NOW_EFFECTS &quot; (get (car active_problems) 'effects)) ;!!!
         )
    )
)
; ************************************************************* 3
; STOP_PROJECTION ends a projection.
; global variable:  effector
(defn stop_projection (projn)
   (setq effector (get projn 'first_effector))
   (cond (trace_prob (my_print  '&quot;Projection &quot; effector '&quot; from &quot;
                                projn '&quot; stopped.&quot;
 
                     )
          )
   )
   ; erase projected effects:
   (put (car active_problems) 'effects
        (remove effector (get (car active_problems) 'effects) )
   )
   ;(my_print '&quot;Now_effects: &quot; (get (car active_problems) 'effects))  ;!!!!
   (put (car active_problems) 'effects_objs
        (remove_mess effector (get (car active_problems) 'effects_objs))
   ) 
   ; punish the rule that started the projection
   ; (punish (list (last (get (car active_problems) projn))))
   (setq active_projections (remove projn active_projections))
)
; ************************************************************************3a
; REMOVE_MESS removes from a message list a message having the given 
; predicate.
(defn remove_mess (conc mess_list)
   (prog (m_lst )
       (setq m_lst mess_list)
       loop
       (cond ( (null m_lst) (return mess_list)))
       (cond ( (equal conc (get_predicate (car m_lst)))
               (return (remove (car m_lst) mess_list))
             )
       )
       (setq m_lst (cdr m_lst))
       (go loop)
   )
)
;*************************************************************************** 4
;  PI_STATUS (PROB CLOC) prints out the current contents of key variables
 
(defn pi_status (prob cloc)
   (my_print '&quot;----------------------------------------------&quot;)
   (my_print  '&quot;PROBLEM:  &quot; prob   '&quot;     TIMESTEP:  &quot; cloc )
   (cond ( print_to_file (print &quot;FIRED &quot; )
                         (print best_rules)
                         (terpri)
                         (print cloc)
                         (terpri)
         )
   )
   (my_print  '&quot;Active messages:  &quot; (remove_confidences active_messages ))
   (my_print  '&quot;Active concepts:  &quot; active_concepts )
   (my_print  '&quot;Concept activations:  &quot;
            (mapcar 'get_activation active_concepts)
  )
   (my_print  '&quot;Active rules:  &quot;    active_rules )
   (my_print  '&quot;Active problem solutions:  &quot; active_solutions)
   (my_print  '&quot;Solution activations:  &quot;
              (mapcar 'get_activation active_solutions)
   )
   (my_print  '&quot;Subgoals:  &quot;   (get (car active_problems) 'sub_goals) )
   (my_print  '&quot;Active projections:  &quot;  active_projections )
)
; ************************************************************************ 4b
; REMOVE_CONFIDENCES returns a list of messages with no confidence value.
(defn remove_confidences (mess_lst)
   (prog (mss result)
      (setq mss mess_lst)
      (setq result nil)
      loop
      (cond ( (null mss) (return (reverse result)) ))
      (setq result (cons (remove (fourth (car mss)) (car mss)) result))
      (setq mss (cdr mss))
   (go loop)
   )
)
;************************************************************************* 5
; OBSERVE:  not yet implemented:  see file world.l
; this will read off messages from a 3-dimensional array environment.
 
;  add to message list from external environment:
(defn observe ()
   (cond ( environment_made
           (my_print '&quot;observing environment&quot;)
         )
    )
)
;  ************************************************************************ 6
;  CONCEPTS_FROM returns a list of all the concepts used in a list of
;  conditions, actions, or messages
(defn concepts_from (mess_list)
   (mapcar 'car mess_list)
)
;
;*************************************************************************** 7
;  CHECK_FOR_SUCCESS checks whether the goals are now all on the
;  message list, i.e. have been accomplished.
;  global variable:  contradiction
(defn check_for_success (problem_name)
;  check that the projections have not produced a contradiction
;  with non-projected messages:  (ignore if doing motivation)
   (setq contradiction
        (contradict projected_messages (get (car active_problems) 'goals))
   )
   (cond ( stop_problem t)  ; set by make_hypothesis in explain.l
         
         ( (and contradiction (not motive_relevance_flag))
           ; add to this:  stop all projections.
           (stop_projection (car (projn_from_mess contradiction)))
           nil ;returned
         )
;   see if all goals have been accomplished:
         (t (cond ( (accomplished (get problem_name 'goals)
                     active_messages
                    )
                    t                     ; return t
                  )
                  ( t (cond ( trace_prob
                              (my_print '&quot;Problem not yet solved&quot;)
                              nil         ; return nil
                            )
                       )
                  )
            )
         )
    )
)
;************************************************************************** 8
 
;  ACCOMPLISHED returns t if all the goals are satisfied by the active
;  messages.
(defn accomplished (goal_list mess_list)
  (setq goals_satisfied nil)
  (prog (lst)
        (setq lst goal_list )
        loop
        (cond ( (null lst) (return t) ) )
        (cond ( (not (is_satisfied (car lst) mess_list))
                (return nil)
              )
        )
        (setq lst (cdr lst) )
        (go loop)
   )
 )
;*************************************************************************** 9
 
;  IS_SATISFIED returns t if a goal is on the message list.
;  a goal can be satisfied by exactly matching a message.  Some goals are
;  more flexible:  one of the form (pred ($?) true) is satisfied  if any
;  object can be shown to be pred.  One of the form (pred (obj_a) ?)
;  is satisfied if any truth value, true or false, is found to
;  hold.
 
(defn is_satisfied (goal mess_list)
  (prog (lst mess)
        (setq lst mess_list)
        loop
        (setq mess (car lst))
        (cond ( (null lst) (return nil) ) )
        (cond ( (and (equal (car goal) (car mess))
                     (arg_equal (second goal) (second mess))
                     (or (equal (third goal) '?)
                         (truth_satisfies mess goal)
                     )
                     ; hypotheses to be explained not satisfied:
                     (not (atom_begins (fifth goal) #\H)) ; for chain_explain
                )
                (setq goals_satisfied (cons goal goals_satisfied))
                (return t)
              )
        )
        (setq lst (cdr lst) )
        (go loop)
   )
  
)
;***************************************************************9a
;  ARG_EQUAL returns true if two sets of arguments are equal or
;  if the goal argument is a satisfied $?.
;  e.g. ( arg_equal ($? $?) (john fred) ) = t.
;
(defn arg_equal (args1 args2)
   (prog (ars1 ars2)
     (cond ( (equal args1 args2) (return t) ) )
     (setq ars1 args1)
     (setq ars2 args2)
     loop
     (cond ( (null ars1) (return t)))
     (cond ( (and (not_equal (car ars1) '$?)      ; open query
                  (not_equal (car ars1) (car ars2) )
             )
             (return nil)
           )
     )
     (setq ars1 (cdr ars1))
     (setq ars2 (cdr ars2))
     (go loop)
   )
)
; ************************************************************************ 9b
; TRUTH_SATISFIES checks whether a goal is satisfied.
 
(defn truth_satisfies (mess1 mess2)
   (and (not_equal (third mess1) 'want_true)
        (not_equal (third mess1) 'want_false)
        (truth_compatible mess1 mess2)
   )
)   
;************************************************************************** 10
 
;  CONTRADICT returns t if any member of the first list is incompatible with
;  any member of the second.
 
(defn contradict (mess_list_1 mess_list_2)
   (prog (lst1 lst2)
         (setq lst1 mess_list_1)
         outloop
         (cond ((null lst1) (return nil)))     ;no contradiction
         (setq lst2 mess_list_2)
             inloop
             (cond ( (null lst2)
                     (setq lst1 (cdr lst1))
                     (go outloop)
                   )
             )
             (cond ( (and (equal (car (car lst1))
                                 (car (car lst2))  ; predicate
                          )
                          (equal (second (car lst1))
                                 (second (car lst2)) ; arguments
                          )
                          (not (truth_compatible (car lst1)
                                                 (car lst2)
                               )
                          )
                          ; ignore &quot;want&quot; truth values:
                          ;(not (or (atom_begins (third (car lst1) #\w))
                          ;         (atom_begins (third (car lst2) #\w))
                          ;     )
                          ;)
                      )
                      (return (car lst1))   ; return offending message
                   )
             )
             (setq lst2 (cdr lst2))
             (go inloop)
    )
)
; ********************************************************************* 11
;  REWARD (rule_list) increases the strength of all rules which
;  have contributed to solving the problem.
 
(defn reward (rule_list)
   (cond ( trace_prob
           (my_print  '&quot;rewarding:  &quot; rule_list )
         )
   )
   (setq rule_list (remove nil rule_list))    ; kluge:  bug in abduction
   (mapcar '(lambda (rul)
               (put rul 'strength
                    (max1 (add (get rul 'strength)
                               incr_stren
                          )
                    )
               )
            )
            rule_list
    )
)
;************************************************************************** 12
;  PUNISH (rule_list) decreases the strength of all rules which
;  have contributed an unsuccessful projection.
 
(defn punish (rule_list)
   (cond ( trace_prob
           (my_print  '&quot;punishing:  &quot; rule_list )
         )
   )
   (mapcar '(lambda (rul)
               (put rul 'strength
                    (min .1  (diff (get rul 'strength)
                                  incr_stren
                              )
                    )
               )
            )
             rule_list
    )
)
; end of prob.l.  See prob_fire for continuation.