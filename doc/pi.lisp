
; PI (Processes of Induction) LISP code. October, 2001
; See P. Thagard, Computational Philosophy of Science, 1988.

; Here are all the files needed to run PI. The first function
; is a patch needed to convert from Sun Common LISP to 
; universal Common LISP.    If you encounter problems,
; email pthagard@uwaterloo.ca.

; CONCAT combines any number of atoms into a long atom.


(defun concat (&rest concat-things) 
   (read-from-string (coerce (apply #'append 
                                    (mapcar #'atom-to-list
                                            concat-things
                                     )
                             )
                             'string
                     )
   )
)

; FILE:        ana_schem.l
; PURPOSE:     analogical schema formation in PI
; PROGRAMMER:  Paul Thagard
; CREATED:     1-30-86
; UPDATED:     1-14-87
; ******************************************
; SCHEM_ALL is called by solve_problem when a problem solution has
; been achieved using an analogous concept solution.  
; old_anas is a list of triples: base target analogous_concepts.
(defun schem_all (prob_name old_anas)
   (prog (triples)
      (setq triples old_anas)
      loop
      (cond ( (null triples) (return t)))
      (schematize (caar triples) prob_name (third (car triples)))
      (setq triples (cdr triples))
      (go loop)
   )
)
; ******************************************
; SCHEMATIZE creates a 
; new, abstract concept solution.  The structure ana is a list of 
; pairs of analogous concepts, set up by analogize in analog.l.
; For globals, see below.

(defun schematize (prob1 prob2 ana)
 (let (schem )
   (setq schema (concat prob1 '/  prob2))
   ; set up variables for assign_vbls:
   (setq assoc_vbls nil)
   (setq avail_vbls vbl_list) 
   ;  set up goals, start, and solution key for schema:
   (put schema 'goals (abstract_list (get prob1 'goals)
				     (get prob2 'goals)
				     ana
		      )
   )
   (put schema 'start (abstract_list (get prob1 'start)
				     (get prob2 'start)
				     ana
		      )
   )
   (cond  ( (get prob1 'explan_status) ; explanation problem
            (put schema 'abductions
                 (abstract_list (get prob1 'abductions)
                                (get prob2 'abductions)
                                ana
                 )
            )
          )
          ( t (put schema 'effects_objs ; ordinary problem
                   (abstract_list (get prob1 'effects_objs)
			          (get prob2 'effects_objs)
				  ana
                   )
              )
          )
   )
   ; schematize analogous rules for problem solving:
   (schem_rules prob1 prob2 ana schema)
   ; associate schema with relevant concepts:
   (setq schema_concs 
	 (conc_from_prob schema)
   )
   (put schema 'attached_concepts schema_concs)
   (store_solution schema schema_concs)
   (setq all_problems (cons schema all_problems))
   (cond ( trace_data 
	   (my_print '"Analogical schema produced: " schema)
	 )
   )
 )
)
; **************************************************************
; STORE_SOLUTION associates concepts with schematic solutions.
(defun store_solution (prob concepts)
    (cond ( (null concepts) nil)
	  (t (put (car concepts) 'old_solutions
		  (cons prob (get (car concepts) 'old_solutions) )
	     )
	     (store_solution prob (cdr concepts) )
          )
    )
)
; ****************************************************************
; ABSTRACT_LIST builds a list of abstract messages out of two lists
; of concrete messages and an already established analogy. 
(defun abstract_list (mess_lst1 mess_lst2 ana)
   (prog (mlst1 mlst2 result first_mess)
      (setq mlst1 mess_lst1)
      (setq mlst2 mess_lst2)
      (setq result nil)
      loop1
      (cond ( (null mlst1)
              (return (union (intersection mess_lst1 mess_lst2)
                             (remove nil result)
                      )
              )
            )
      )
      (setq mlst2 mess_lst2)
      ; check the first message against all messages in 2nd list
      loop2
      (cond ( (null mlst2) 
	      (setq mlst1 (cdr mlst1))
	      (go loop1) 
	    )
      )
      (setq result (union (abstract_mess (car mlst1) (car mlst2) ana )
			  result
		   )
      )
      (setq mlst2 (cdr mlst2))
      (go loop2)
   )
)
; ********************************************************
; ABSTRACT_MESS forms an abstraction from two messages, returning
; nil if nothing interesting results.  
; Global variable:  abstrns.
;
(defun abstract_mess (mess1 mess2 ana)
    (cond ( (and (truth_compatible mess1 mess2)
		 (equal (length (second mess1)) (length (second mess2)))
		 (analogous (car mess1) (car mess2) ana)
		 (setq abstrns (related? mess1 mess2) )
	    )
            (prog (abs result)
                  (setq result nil)
                  (setq abs abstrns)
                  loop
                  (cond ( (null abs) (return result)))
   	          (setq result 
                        (cons (list (car abs)
                                    (assign_vbls (second mess1) (second mess2))
                	            (de_project_val (third mess1))
                                    (cond ( (equal (fourth mess1)
                                                   (fourth mess2)
                                            )
                                            (fourth mess1)
                                          )
                 	            )
	                      )
                              result
                        )
                  )
                  (setq abs (cdr abs))
                  (go loop)
             )
          ) 
	  
	  (t nil)
     )
)
    
; ***********************************************************
   
; ANALOGOUS checks to see whether two concepts have been determined 
; to be related in a given analogy.
(defun analogous (conc1 conc2 ana)
   (or (equal conc1 conc2)
       (memberlist (list conc1 conc2) ana)
       (memberlist (list conc2 conc1) ana)
   )
)
; ************************************************************
; RELATED? checks whether two messages are abstractible, i.e. share a
; more abstract concept drawn from the originals.  
; Identical concepts require no further abstraction.
; It first tries to
; abstract the concepts, then tries the objects.
; Returns a set of abstracted concepts.
(defun related? (mess1 mess2)
   (cond ( (equal (car mess1) (car mess2)) (list (car mess1)))
         (t (or (abstract_conc (car mess1) (car mess2) )
	        (abstract_objs (second mess1) (second mess2))
            )
         )
   )
)   
; *************************************************************
; ABSTRACT_CONC finds an abstraction from two concepts based on their
; rules.  If A --> C, and B --> C, then C is an abstraction of both
; A and B.  E.g. animal is an abstraction of cats and dogs, because
; all cats and dogs are animals.  Obviously, there can be more than
; one abstraction.
; More thoroughly, we could do a search up the default 
; hierarchy, so that if A --> D --> C, and B --> E --> C, then C
; would be an abstraction.  This would be done implicitly by 
; abstract_objs, since rule firing would have led to the 
; conclusions that follow.
(defun abstract_conc (conc1 conc2)
    (intersect (possible_abstrns conc1)
	       (possible_abstrns conc2)
    )
)
; **************************************************************
; POSSIBLE_ABSTRNS looks through the rules attached to a concept C
; for simple ones of the form C --> A, returning A as a possible
; abstraction.
(defun possible_abstrns (conc)
   (prog (rules result )
      (setq rules (get conc 'rules))
      (setq result nil)
      loop
      (cond ( (null rules) (return result) ) )
      (cond ( (and (equal (length (get (car rules) 'conditions)) 1)
		   (equal (caar (get (car rules) 'conditions)) conc)
	      )
	      (setq result
		    (cons (caar (get (car rules) 'actions)) result)
	      )
	    )
      )
      (setq rules (cdr rules))
      (go loop)
   )
)
; ***********************************************************
; ABSTRACT_OBJS finds some abstract property of two objects.
; Won't work until objects are upgraded in begin.l and prob_fire.l.
(defun abstract_objs (obj_lst1 obj_lst2)
   (cond ( (or (greaterp (length obj_lst1) 1)
	       (greaterp (length obj_lst2) 1)
	   )
	   nil
	 )
	 ( t (common_properties (car obj_lst1) (car obj_lst2)) )
    )
)
; **************************************************************
; COMMON_PROPERTIES returns the properties that two objects have
; in common.  Need to add proper definition of objects in begin.l
; and updating of objects by prob_fire.l.
(defun common_properties (obj1 obj2)
   (intersect (concepts_from (unary_preds (get obj1 'messages)))
              (concepts_from (unary_preds (get obj2 'messages)))
   )
)
; **************************************************************
; UNARY_PREDS returns a list of only 1-place predicates from a list
; of messages.
(defun unary_preds (mess_list)
   (prog (mess_lst result)
      (setq mess_lst mess_list)
      (setq result nil)
      loop
      (cond ( (null mess_list) (return result) ))
      (cond ( (equal (length (second (car mess_lst) 1) ) )
	      (setq result (cons (caar mess_lst) result))
	    )
      )
   )
)	 
; *************************************************************
; ASSIGN_VBLS keeps variable assignment straight in setting up an
; abstraction.  It uses an association list: 
; ( (val1 vbl1) (val2 vbl2) ...).
; Uses global variables vbl_list set up in begin.l, plus:
; avail_vbls assoc_vbls new_assign.
(defun assign_vbls (arg_lst1 arg_lst2)
    (prog (args1 args2 result)
       (setq args1 arg_lst1)
       (setq args2 arg_lst2)
       (setq result nil)
       (cond ( (equal args1 args2) (return args1)))
       loop
       (cond ( (null args1) (return (reverse result)) ) )
       (setq new_assign (or (cadr (assoc (car args1) assoc_vbls))
			    (cadr (assoc (car args2) assoc_vbls))
			)
       )
       ; if the value is already associated with a variable, use the vbl.
       (cond ( new_assign
	       (setq result (cons new_assign result) )
	     )
	     ; otherwise, assign a new variable:
	     ( t (setq result (cons (car avail_vbls) result) )
		 (setq assoc_vbls 
		       (cons (list (car args1) (car avail_vbls))
			     (cons (list (car args2) (car avail_vbls))
				   assoc_vbls
			     )
		       )
		 )
		 (setq avail_vbls (cdr avail_vbls))
	     )
       )
       (setq args1 (cdr args1))
       (setq args2 (cdr args2))
       (go loop)
   )
)
; *************************************************************
; DE_PROJECT_VAL returns  simple truth value with proj
; stripped of.
(defun de_project_val (val)
    (case val
          ('proj_true 'true)
          ('proj_false 'false)
          ('want_true 'true)
          ('want_false 'false)
          ('true 'true)
          ('false 'false)
     )
)
; ************************************************************
; SCHEM_RULES produces schematic forms of rules attached to two
; problem solutions.
(defun schem_rules (pro1 pro2 ana schem)
    (prog (ruls)
       (setq ruls (get pro1 'rules))
       loop
       (cond ( (null ruls) (return 'DONE)))
       (schem_rule (car ruls) pro2 ana schem)
       (setq ruls (cdr ruls))
       (go loop)
    )
)
; *************************************************************
; SCHEM_RULE looks for schematizable versions of a rule.
(defun schem_rule (rul prob ana schem)
   (prog (ruls related_actns related_condns result)
      (setq related_actns nil 
            related_condns nil
            result nil
      )
      (setq ruls (get prob 'rules))
      loop
      (cond ( (null ruls) (return result)))
      (setq rul1 (car ruls))
      (setq related_condns 
            (abstract_list (get rul 'conditions)
                           (get rul1 'conditions)
                           ana
            )
      )
      (setq related_actns
            (abstract_list (get rul 'actions)
                           (get rul1 'actions)    
                           ana
            )
      )
      (cond ( (and related_condns related_actns)
              (make_rule_long schem
                              related_condns
                              related_actns
                              (get rul 'slot)
                              (get rul 'status)
                              (get rul 'strength)
              )
              (setq result (cons (car all_rules) result))
            )
      )
      (setq ruls (cdr ruls))
      (go loop)
   )
)
   
			      
			      
			      
; *************************************************************
; END OF ANA_SCHEM.L


; FILE:       analog.l
; PURPOSE:    analogical problem solving
; PROGRAMMER: Paul Thagard
; CREATED:    10-24-85
; UPDATED:    1-14-87
; Analogical problem solving works in the following stages.
; 1.  Solve problem P1.
; 2.  Store solution to P1 with relevant concepts.
; 3.  Start solution of P2, the target problem.
; 4.  Spreading activation leads to activation of concepts
;     to which P1 is linked, hence to P1, the base problem.
; 5.  If P1 is sufficiently active, trigger analogical problem
;     solving.  
; 6.  Map from P1 to P2 using record of activation patterns.
; 7.  Use information from mapping to start a new
;     subproblem to try to apply what worked in P1 to P2.
; 8.  Solve P2.
; *****************************************************************
; Global variables in this module:  best_prob analogous_concepts
; analogous_objects key_effectors 
; constant:
(setq min_prob_activation .55)
; ******************************************************************
; TRIG_ANALOG is called by solve_problem.  It checks to see whether
; there are any active problems that might be useful analogs.
; It looks only at the most active problem.
(defun trig_analog (prob problem_list)
   (cond ( problem_list
           (setq best_prob (highest problem_list 'activation))
           (cond ( (greaterp (get best_prob 'activation) 
                             min_prob_activation
                   )
                   (analogize best_prob prob)
                 )
           )
        )
   ) 
)
; *******************************************************
; ANALOGIZE maps between two problems and constructs a new
; approach to the target problem.
(defun analogize (base target)
   
   ; find analogous concepts, which must exist or else activation
   ;   would not be above threshold
   (setq analogous_concepts (trace_concepts base target))
   ; find analogous objects, instantiating analogous concepts
   (setq analogous_objects (trace_objects analogous_concepts base target )) 
   ; note what effectors or hypotheses were the key to solution of base 
   ;    problem.
   (setq key_effectors (get_effectors base))
   (setq key_hypotheses (get base 'abductions))
   ; announce and note analogy:
   (print_analogy base target analogous_concepts
                  analogous_objects key_effectors
   )
   (put (car active_problems) 'analogies_used
        (union (list (list base target analogous_concepts))
              (get (car active_problems) 'analogies_used)
        )
   )
   ; reconstruct target problem
   (reconstruct base target key_effectors key_hypotheses
                analogous_concepts analogous_objects
   )	
   ; activate rules for solution of base
   (setq active_rules (union active_rules (get base 'rules)))
	
)    
; **********************************************************
; TRACE_CONCEPTS returns a list of pairs of associated concepts.
; The associations were set up by execute_actions 
; and build_sub_goals in prob_spread.l.
; There when a concept became active, it was noted what concepts had
; led to its activation.  This looks at the concepts used in the
; base and in the target, and identifies what concepts in the
; target led to the activation of which concepts in the base,
; establishing the mapping between them.  E.g. in the ray problem,
; capture leads to the activation of destroy in the fortress problem,
; so (capture destroy) is one member of the list returned.
(defun trace_concepts (base target)
   (prog (base_concepts target_concepts first_conc act_orgins result)
      (setq base_concepts (conc_from_prob base))  ; see store.l
      (setq target_concepts (conc_from_prob target))
      (setq result nil)
      loop
      (cond ( (null base_concepts) (return result)))
      (setq first_conc (car base_concepts))
      ; find what led to activation of first_conc
      (setq act_origins (find_act_origins first_conc base target ))
	 
      ; look for originating concepts that are in target_concepts
      (setq result (union result
                          (pair_up first_conc act_origins target_concepts)
                   )
      )
      (setq base_concepts (cdr base_concepts))
      (go loop)
   )
)
; *********************************************************
; FIND_ACT_ORIGINS finds the concepts that originated the activation
; of a given concept, using the activation records set up by execute_actions
; and build_sub_goals in prob_spread.l.  To avoid infinite loops, it is
; crucial to distinguish between paths of activation by rule-firing and
; paths of activation by sub-goaling.   In the former case, activation
; records are stored with the property forward_activated_by; 
; in the latter, with 
; goal_activated_by.  
; Multiple paths of activation are possible, resulting in multiple
; mappings.  If the concept was already in the base problem,
; no activation path was necessary.
; for debugging:
(setq activn_debug nil)
(defun find_act_origins (conc base target)
      ; if concept was in both problems, it activated itself.
      (cond ( (member conc (concepts_from (mess_from_prob target)))
              (list conc)
            )
            ; otherwise get forward and backward origins:
            (t (union (direction_find_origins conc base target 
                                              'forward_activated_by
                      )
                      (direction_find_origins conc base target
                                              'goal_activated_by
                      )
                )
             )
       )
)
            
; *************************************************************
; DIRECTION_FIND_ORIGINS looks for activation origins in one
; direction, either forward (rule firing and ordinate spread)
; or backward by subgoaling.
(defun direction_find_origins (conc base target direction)
   (prog (still_to_expand first_conc activ_prop expanded result)
      (if activn_debug (my_print '"Debugging " conc '" " direction))
      (setq activ_prop direction) ; note source of activation
      (setq still_to_expand (get conc activ_prop))
      (setq expanded nil)
      (setq result nil)
      ; search for originating concept:
      loop
      (cond ( (null still_to_expand) (return (remove-duplicates result))))
      (setq first_conc (car still_to_expand))
      (if activn_debug (my_print first_conc still_to_expand expanded))
      ; if first_conc was in target, it was source of activation
      ;  also must have same # of arguments.
      (cond ( (and (member first_conc (conc_from_prob target))
                   (same_arg_size conc first_conc)
              )                  
              (setq result (cons first_conc result))
              ; kluge to prevent getting additional silly analogs FIX:
              (return result)
            )
      )
      ; check to avoid infinite loops:
      (cond ( (member first_conc expanded) 
              (setq still_to_expand (remove first_conc still_to_expand))
              (go loop)
          )
      )
      ; if concept was activated by other concepts, add them to
      ; the list with new ones to be checked first.
      (cond ( (get first_conc activ_prop)
              (setq still_to_expand 
                    (union (reverse (get first_conc activ_prop))
                           still_to_expand
                    )
              )
              (setq expanded (cons first_conc expanded))
            )
      ; otherwise, the concept was an originator
            (t (setq result (cons first_conc result)))
      )
      (setq still_to_expand (remove first_conc still_to_expand))
      (go loop)
   )
)
; ********************************************************
; SAME_ARG_SIZE checks if two concepts are both n-place.
(defun same_arg_size (conc1 conc2)
   (if (or (null (get conc1 'instances))
             (null (get conc1 'instances))
       )
       t
       ;else
       (equal (length (second (car (get conc1 'instances))))
              (length (second (car (get conc2 'instances))))
       )
   )
)
         
; *********************************************************
; PAIR_UP takes a concept, a list of concepts, and another list of concepts.
; Any member of the first list which is also a member of the second list
; is paired with the original concept.
; Example:  (pair_up 'a '(b c d) '(c d)) -> ( (a c) (a d))
(defun pair_up (conc list1 list2)
   (prog (lst1  first result)
      (setq lst1 list1)
      (setq result nil)
      loop
      (cond ( (null lst1) (return result)))
      (setq first (car lst1))
      (cond ( (member first list2)
              (setq result (cons (list conc first) result))
            )
      )
      (setq lst1 (cdr lst1))
      (go loop)
   )
)
; ************************************************************
; TRACE_OBJECTS finds similar pairs of analogous objects.
; o1 in the base is paired with o2 in the target if o1 has
; some concept c1 that has been traced to some c2 that the problem
; description says applies to o2.
; Example:  in the ray problem, o_army gets paired with o_tumor,
; because army has been associated with tumor.
; Note:  takes a list of pairs of concepts, and returns a list
;        of pairs of objects.	 		
(defun trace_objects (list_of_concept_pairs base target)
   (prog (lst result conc1 conc2)
      (setq lst list_of_concept_pairs)
      (setq result nil)
      loop
      (cond ( (null lst) (return (remove_duplicates result))))
      (setq conc1 (caar lst))
      (setq conc2 (second (car lst)))
      (setq result (union result
                          (pair_obj_up conc1 conc2 base target)
                   )
      )
      (setq lst (cdr lst))
      (go loop) 
   )
)
; **********************************************************
; PAIR_OBJ_UP pairs each object that the base says has concept1
; with an object that the target says has concept2.
(defun pair_obj_up (concpt1 concpt2 prob1 prob2)
    (make_pairs (objects_from concpt1 prob1)
                (objects_from concpt2 prob2)
    )
)
; ********************************************************
; OBJECTS_FROM returns a list of objects associated with a 
; concept in the given problem.
(defun objects_from (conc prob)
    (prog (mess_list first_mess)
       (setq mess_list (mess_from_prob prob))
       loop
       (cond ( (null mess_list) (return nil)))
       (setq first_mess (car mess_list))
       (cond ( (and (equal conc (get_predicate first_mess))
                    (or (equal (third first_mess) 'true)
                        (equal (third first_mess) 'want_true)
                    )
               )
               (return (get_argument first_mess))
             )
       )
       (setq mess_list (cdr mess_list))
       (go loop)
    )
)
; **********************************************************
; MESS_FROM_PROB returns the relevant messages from a problem.
(defun mess_from_prob (prob)
    (union (get prob 'goals)
           (get prob 'start)
    )
)
; **************************************************************
; MAKE_PAIRS takes two lists, and returns a list of pairs,
; with the nth atom of list1 paired with the nth of list2.
(defun make_pairs (lst1 lst2)
   (cond ( (not_equal (length lst1) (length lst2)) nil)
         ( (null lst1) nil )
         ( t (cons (list (car lst1) (car lst2))
                   (make_pairs (cdr lst1) (cdr lst2))
             ) 
         )
   )
)
; ***************************************************************
; GET_EFFECTORS looks to see what effectors were instrumental in
; solving a problem.  Currently, this is very simple, looking at
; all the effectors that were used in solving a problem.  These are
; noted by update_effects in prob_fire.l.
; A more sophisticated approach would require some causal analysis,
; to determine which of the effectors used were most valuable.
; Cf. explanation-based learning.
(defun get_effectors (prob)
   (get prob 'effects_objs)
)
; ****************************************************************
; PRINT_ANALOGY announces the found analogy.
(defun print_analogy (base target ana_conc ana_obj effects)
   (cond ( trace_prob
           (my_print '"Analogy found between " base " and " target )
           (my_print '"Analogous concepts: " ana_conc)
           (my_print '"Analogous objects:  " ana_obj)
           (my_print '"Key effectors:      " effects)
           (my_print '"Activating rules:   " (get base 'rules))
         )
   )
)
; ****************************************************************
; RECONSTRUCT reconstructs the target problem.  Currently, this consists
; of setting new subgoals based on key effectors in the base and the
; mapped objects.  
; A more sophisticated technique would be to start a whole new sub-problem,
; e.g. how to split a ray-beam.
; In either case, the result is a kind of decomposition of the target problem
; based on the structure of the base problem.  Nice, huh?
; <<Major weakness:  should do more analysis to figure out what are the 
;   responsible effectors or hypotheses.>>
(defun reconstruct (base target effects hypotheses ana_concs ana_objs) 
   (cond ( hypotheses
           (reconstruct_hyps base target hypotheses ana_concs ana_objs)
         )
   )
   (prog (effs first_eff eff_objs new_sub_goal)
      (setq effs effects)
      loop
      (cond ( (null effs) (return t)))
      (setq first_eff (car effs))
      ; find what objects to do the effect on:
      (setq eff_objs (find_associates (second first_eff)
                                      ana_objs
                    )
      )
      ; set a new sub-goal to do the effect:
      (setq new_sub_goal (list (car first_eff)
                               eff_objs
                               'want_true
                         )
      )
      (put target 'sub_goals (cons new_sub_goal 
                                   (get target 'sub_goals)
                             )
      )
;     activate concept from subgoal:
      (put (car new_sub_goal) 'activation
           (my_max 1
                   (add .6 (get (car new_sub_goal) 'activation))
           )            ; arbitrary number
      )
      (setq active_concepts (cons (car new_sub_goal)
                                        active_concepts
                            )
      )
      (cond ( trace_prob    
	      (my_print '"New sub-goal:  " new_sub_goal)
            )
      )
      (setq effs (cdr effs))
      (go loop)
   )
)
; *************************************************************
; FIND_ASSOCIATES takes a list of objects, and returns a list of
; their associates, based on an association list.
(defun find_associates (lst assoc_lst)
   (prog (ls result)
       (setq ls lst)
       loop
       (cond ( (null ls) (return (reverse result)) ))
       (setq result (cons (second (assoc (car ls) assoc_lst))
                          result
                    )
       )
       (setq ls (cdr ls))
       (go loop)
    ) 
)
; *************************************************************
; FOR ANALOGICAL ABDUCTION:
; *************************************************************
; RECONSTRUCT_HYPS is like reconstruct, except that instead of 
; building sub-goals on the basis of past effects, it builds new
; hypotheses on the basis of past abduced hypotheses.
; <<Should screen hypotheses to rule out ones that were superceeded
;   by other members of the set that proved to be better explanations.>>
(defun reconstruct_hyps (base target hypoths ana_concs ana_objs)
   (prog (hyps ana_hyp)
      (setq hyps hypoths)
      loop
      (cond ( (null hyps) (return t)))
      (setq ana_hyp (or (tight_analog_hypoth base target 
                          (caar hyps) ana_concs ana_objs
                         )
                         (loose_analog_hypoth (caar hyps) ana_concs 
                                              analogous_objects ; kludge
                         )
                     )
      )
      (cond ( ana_hyp
              (make_hypothesis ana_hyp target base  'Analogical)
            )
      )
      (setq hyps (cdr hyps))
      (go loop)
   )
)
; *************************************************************
; TIGHT_ANALOG_HYPOTH constructs a new hypothesis analogous to an old
; one.
; This uses a detailed mapping between problems to construct 
; well-developed analogies.
; Global vbls:  new_conc new_args hyp_mess new_mess
(defun tight_analog_hypoth (base target hyp ana_concs ana_objs)
    (setq hyp_mess hyp)  ;correction from earlier:  hyp is mess already
    ; construct new predicate:
    (setq new_conc (second (assoc (car hyp_mess) ana_concs)))
    ; construct new arguments
    (setq new_args (find_associates (second hyp_mess) ana_objs))
    (cond ( (and new_conc new_args)
            (setq new_mess 
                  (list new_conc
                        new_args
                        (third hyp_mess)
                        .1
                  )
            )
            ; make sure explanation not circular, i.e. explaining itself:
            (cond ( (circular new_mess base target) nil)
                  ; return message
                  ( t (name_message new_mess 'hypothesis))
            )
          )
          (t nil) ; return nil if nothing formed
    )
)
; *************************************************************
; CIRCULAR checks that a new hypothesis isn't equivalent to
; one of the explananda.  If it is, the base problem is listed as
; useless, and de-activated by prob_spread.l.
(defun circular (mess base target)
   (cond ( (mess_on mess (get target 'goals) 'sought)
           (my_print '"Circular hypothesis rejected: " mess)
           (my_print '"Failed analogy: "  base)
           (put target 'bad_ana_problems 
                (union (list base) (get target 'bad_ana_problems))
           )
         )  
         (t nil)
   )
)
; *************************************************************
; LOOSE_ANALOG_HYPOTH constructs a new hypothesis analogous to an old
; one.
; This uses any possible mapping between problems to construct 
; well-developed analogies.  Currently a bit klugy.
; Global vbls:  new_conc new_args hyp_mess new_mess
(defun loose_analog_hypoth (hyp ana_concs ana_objs)
    (setq hyp_mess hyp)   
    ; construct new predicate - cheap:
    (setq new_conc (car hyp_mess))
    ; construct new arguments - cheap:
    (setq new_args (find_loose_associates (second hyp_mess) ana_objs))
    (cond ( (and new_conc new_args)
            (setq new_mess 
                  (list new_conc
                        new_args
                        (third hyp_mess)
                        .1
                  )
            )
            (cond ( (circular new_mess base target) nil)
                  ; return message
                  ( t (name_message new_mess 'hypothesis))
            )
          )
          (t nil) ; return nil if nothing formed
    )
)
    
; *************************************************************
; FIND_LOOSE_ASSOCIATES takes a list of objects, and returns a list of
; their associates, based on an association list.
; If no associate available, will use existential variable, set up
; by reconstruct hyps
(defun find_loose_associates (lst assoc_lst)
   (prog (ls result ex_vbl)
       (setq ls lst)
     
       loop
       (cond ( (null ls) (return (reverse result)) ))
       (setq result 
             (cons (cond   ( (second (assoc (car ls) assoc_lst)))
                           (t (setq ex_vbl (car exist_vbls))
                              (setq analogous_objects ; kluge!
                                    (cons (list (car ls) ex_vbl)
                                          analogous_objects
                                    )
                              )
                              (setq exist_vbls (cdr exist_vbls))
                              ex_vbl
                            )
                         
                    )
                    result
             )
       )
       (setq ls (cdr ls))
       (go loop)
    )
 
)
; *************************************************************

; End of analog.l.;  FILE:          begin.l
;  PURPOSE:       Central file for system PI (Processes of Induction)
;                 Program written in Common Lisp, running on a Sun 3/75
;                 under UNIX.
;                 Includes functions for running system
;                 and functions for making
;                 the central  data structures of PI:  concepts,
;                 rules, objects, problems.
;  PROGRAMMER:    Paul Thagard
;  CREATED:       5-23-84
;  LAST UPDATED:  5-23-88
;  NOTE:  PI is copyright (c) 1988 Paul Thagard.  Permission is 
;  granted to use it for research purposes, but denied for
;  commercial and military purposes.
;  This is the Common LISP version.
; *********************************************************
   (my_print "Welcome to PI.  This program is copyright (c) 1988 Paul Thagard.")
   (my_print "Permission is hereby granted for use for research purposes,")
   (my_print "   but denied for commercial or military purposes.")
   (my_print "It comes with no warranty.")
;**********************************************************
 
;  PI   files:         (add suffix ".l")
;       analog       analogical problem solving
;       ana_schem    analogical schema formation
;       begin        initialization and data structure creation
;       cause        causal analysis  (not for distribution)
;       common       conversion to common lisp
;       concepts     concept formation
;       explain      explanation and abduction
;       gen          generalization:  synchronic rule learning
;       misc         miscellaneous utility functions
;       motiv        motivated inference 
;       prob         problem solving
;       prob_fire    problem solving:  firing rules
;       prob_spread  problem solving:  spreading activation
;       store        storing and retrieving messages and problems
;       theory       inference to the best explanation
;       trig         triggering conditions
;       world        simulated world (not for distribution)
;       wts          input file:  discovering the wave theory of sound
; *************************************************************
; TO RUN PI, LOAD ALL THE ABOVE FILES AND A DATA FILE MODELED ON
; WTS.L
; **************************************************************
;       data files:  some not yet transferred into franz
;                    most not transferred into common
;
;       for distribution, the file wts is included to simulate
;       discovery of the wave theory of sound.
;       
;       data/abd        sample data for abduction
;       data/abd_rul    data for abduction to a rule
;       data/adair      schema formation
;       data/ana_schem  data for analogical abduction
;       data/class      sample data for classification
;       data/cup        input data for cup & paper problem
;       data/breed.l    analogical abduction
;       data/exist.l    existential abduction
;       data/fem-banl.l conceptual combination
;       data/fort.l     problem solving by analogy
;       data/gen_lon    data for generalization with relations
;       data/ray        data for ray problem - analogy
;       data/spec       input data for specialization
;       data/theor      data for theory evaluation
;       data/theor2     theory evaluation
;       data/wts1       data for propagation -> wave theory of sound
;       data/wts2       data for reflection -> wave theory of sound
;       data/wts3       data for propagation & reflection -> wave theory
;       data/wts4       data for discovery and rejection of ball theory
;       data/wts5
;       data/wts.big    wave theory of sound
;       data/yuppy      input data for concept formation
;       pi.d1        sample data for conceptual combination
; *******************************************************
;  run_pi initializes the system setting these parameters:
;    1.  trace_data:  produces a trace of creation of concepts
;                     and rules.
;    2.  trace_prob:  traces problem solving by printing out system
;                     status at each time step.
;    3.  max_rules:   the maximum number of rules to be fired at once.
;    4.  deact_conc:  the amount a concept is deactivated per time step.
;    5.  min_activ:   the minimum amount a concept must be activated to
;                     remain on active_concepts.
;    6.  incr_activ:  determines the extent to which a concept is activated
;                     as the result of the strength of the rule which
;                     fired it.
;    7.  incr_stren:  the amount a successful rule has its strength
;                     increasedata/
;    8.  timesteps:   maximum number of steps in problem solving
;
;  a typical call would be (run_pi 'true nil 5 .1 .2 .5 .1 50)
 
(defun run_pi (trace_data? trace_prob? max_rules?  deact_conc?
               min_activ?  incr_activ? incr_stren? timesteps?
              )
   (setq all_rules        nil      ; system information
         all_concepts     nil
         all_problems     nil
         generic_concepts nil
         all_objects      nil
         all_goal        nil
         all_hypothesis  nil
         all_explanandum nil         
    
         active_concepts    nil     ; data structures
         active_rules       nil
         active_messages    nil
         active_problems    nil
         active_solutions   nil
         active_projections nil
         known_messages     nil
         projected_messages nil
         best_rules         nil
         trace_data      trace_data?        ; parameters
         trace_prob      trace_prob?
         max_rules       max_rules?
         deact_conc      deact_conc?
         min_activ       min_activ?
         incr_activ      incr_activ?
         incr_stren      incr_stren?
         timesteps       timesteps?
 
 
         ; flags for system functioning:
         goals_to_messages       nil        ; make want_true messages
         go_backwards            t          ; use subgoals
         world_made              nil        ; artificial environment
         trig_flag               t          ; trigger inductions
         analogy_flag            t          ; trigger use of analogy
         motive_relevance_flag   nil        ; see motiv.l.
         rel_motiv_flag          nil        ;      "
         chain_explain_flag      nil        ; see concepts.l
         conc_to_explain_with    nil        ;      "
	 
         ; constants:
         confidence_threshold   .5
         ; available variables:
         univ_vbls    '($x $y $z $u $v $w $d $e $f)  ; universal
         exist_vbls   '(%x %y %z %u %v %w %a %b %c %d %e %f %g %h)  ; existential
         all_exist_vbls '(%x %y %z %u %v %w %a %b %c %d %e %f %g %h) 
    	 vbl_list      (union univ_vbls exist_vbls  ) 
   )
   (setq debug nil)
   
   (my_print '"PI initialized.")
)
;  to make life easy, just call run which sets defaults:
(defun run (steps)
   (run_pi 'true 'true 10  .1 .001 1 .2 steps)
)
;**********************************************************
 
;**********************************************************
;*    functions for creating data structures:             *
;**********************************************************
;  MAKE_PROBLEM constructs a problem with goals and starting conditions:
 
(defun make_problem (problem_name start_list goal_list type)
   (setq all_problems (cons problem_name all_problems))
   (put problem_name 'goals 
        (name_mess_list goal_list type)
   ) 
   (put problem_name 'data_type 'problem)
   (put problem_name 'start start_list)
   (put problem_name 'activation 0)
   (cond ( trace_data
           (my_print '"Problem made:  " problem_name)
         )
   )
)
 
;  ************************************************************
 
;  assorted junk:
 
(defun make_condition (pred)
    (list pred '($x) 'true )
)
(defun make_action (pred)
    (list pred '($x) 'true  'deduce)
)
 
; ************************************************************
; PROJECTS checks whether any of the actions of a rule are effectors
; that would start projections.
(defun projects (actions)
   (cond ( (null actions) nil)
         ( (equal (get_effect_status (car actions)) 'effect) t)
         ( t (projects (cdr actions)))
   )
)
;  ************************************************************
 
;  MAKE_RULE constructs a simple rule using six fields:
;  the concept to which the rule is to be attached
;  the predicate for the condition, the predicate for the action,
;  the status (e.g. default), and the strength.
;  this should be generalized to allow rule to be attached to
;  more than one concept.
 
(defun make_rule (conct pred1 pred2 slo stat stren )
   (make_rule_long conct
                   (list (make_condition pred1))
                   (list (make_action pred2)) 
                   slo stat stren
   )
)
;  *******************************************************
 
;  MAKE_RULE_LONG construct more complex rules, allowing predicates
;  with any number of arguments, and any number of conditions and
;  actions.  The cost of using it is that conditions and actions must
;  be specified in full.
 
(defun make_rule_long (conct condns actns slo stat stren )
   (prog (result)
      (cond ( (redundant condns
                         actns
                         all_rules
              )
              (return nil)     ;  no rule made
            )
      )
      (setq result (concat (newsym 'r_) '_ conct))
      (put result 'data_type 'rule)
      (put result 'actions actns)
      (put result 'conditions condns)
      (cond ( (projects actns) (put result 'proj_status t) ) )
      (put result 'status    stat)
      (put result 'strength  stren)
      (put result 'slot slo)
      (put result 'activation .1)
      (put result 'current_value .1)
      (put result 'attached_concepts (list conct) )  ; expand, to have 
;                     multiple attachments and degrees of attachment
      (setq all_rules (cons result all_rules))
      (cond ( trace_data
              (my_print '"Rule made: "  result)
              (my_print '"  "  (concepts_from condns) '" -> " 
                        (concepts_from actns)
              )
	    
            )
       )
       ; set up simple concepts for those not already done:
       (make_concept_s (concepts_from (append condns actns) ))
       (put conct 'rules (cons result
                               (get conct 'rules)
                         )
       )
       (return result)
   )
)
 
;  *******************************************************
;  REDUNDANT checks to see whether a rule to be made already existed,
;  by checking whether its conditions and actions already belong
;  to some rule on the given list.
 
(defun redundant (condns actns  rule_list)
   (cond ( (null rule_list) nil)
         ( (and (equal condns (get (car rule_list) 'conditions))
                (equal actns (get (car rule_list) 'actions))
           )
           t
         )
         (t (redundant condns actns  (cdr rule_list)))
   )
)
;  *******************************************************
 
;  MAKE_CONCEPT constructs a concept named "conct" with lists of
;  superordinates, subordinates, instances, rules, and degree of activation.
 
 
(defun make_concept (conct superord subord inst ruls activn)
;  check for redundancy:
   (declare (special conct))
   (cond ( (member conct all_concepts)
           nil                     ; no concept made
         )
         ( t                       ; otherwise, make concept:
 
           (cond ( trace_data (my_print '"Concept made: " conct)))
           (put conct 'superordinates superord)
           (put conct 'rules ruls)
           (put conct 'data_type 'concept)
           (setq all_concepts (cons conct all_concepts))
           ;  revise subordinates of superordinate and make rules:
           (mapcar '(lambda (super)
                       (put super 'subordinates
                            (cons conct (get super 'subordinates))
                       )
                       (make_rule conct conct super 'superordinate 'actual '.7)
                     )
                     superord
           )
           (put conct 'subordinates subord)
           (put conct 'instances inst)
           (put conct 'activation activn)
           conct 
         ) 
   )  
)
 
 
;  ************************************************************
;  MAKE_CONCEPT_S makes many simple concepts with no information.
(defun make_concept_s (lst)
   (mapcar '(lambda (concpt)
                (make_concept concpt nil nil nil nil 0)
            )
           lst
   )
)
;  ************************************************************
 
;  MAKE_OBJECT (name list) constructs an object whose property list contains
;  entries bases on the elements of list.  thus (make_object obj_1
;  (  (kind robin .7) (color red .9) )) puts two properties on
;  the property list of obj_1.  the number .7 indicates how typically
;  the object has the property.  a value of 0 indicates that the
;  does not have the property.
;  this function also updates the list of instances of the
;  properties, storing obj_1 as one of the instances of robin and red
;  if the name given is nil, a new object name is generatedata/
(defun make_object (name lst)
   (cond ( (null name)
           (setq obj_name (newsym 'obj_))
           (intern obj_name)
         )
         (t (setq obj_name name))
   )
   (prog (l property)
         (setq l lst)
         loop
         (cond ( (null l)  (return '"object made") ) )
         (setq property (car l))
         (setq all_objects (cons obj_name 'all_objects))
         (put obj_name (car property) (cdr property))
         (put (second property) 'instances
              (cons (list obj_name (third property))
                    (get (second property) 'instances)
              )
          )
          (setq l (cdr l))
          (go loop)
    )
)
;  ************************************************************
;  functions for dealing with messages:
(defun get_predicate (mess)
   (car mess)
)
 
(defun get_argument (mess)
   (second mess)
)
 
(defun get_truth (mess)
    (third mess)
)
 
(defun get_confidence (mess)
    (cond ( (fourth mess) (fourth mess) )
          ( t 1)       ; default confidence is 1)
    )
)
(defun get_effect_status (actn)
    (fourth actn)
)
(defun projn_from_mess (mess)
    (cond ( (listp (fifth mess)) (fifth mess))
          ( t (list (fifth mess)))
    )
)
; Note:  most messages have confidence in fourth place;
; actions in rules to be defined have effector status:
; effect or deduce.
;  ************************************************************


; FILE:         cause.l
; PURPOSE:      causal reasoning
; PROGRAMMER:   Paul Thagard
; CREATED:      9-1-86
; UPDATED:      9-2-86
; **************************************************************
; MAKE_EVENT sets up an event structure:
;            Event-name:
;               data_type:     'event
;               time:          (start end)
;               space:         ( (x1 x2)  (y1 y2)  (z1 z2))
;               descriptions:  (messages)
;               causes:       (events)
;               effects:     (events)   
;
; Note:  start and end are integers 0 ... .  x1 etc. are also integers, 
; correspoding to axes in three dimensions.
; Other information to be added:  what heuristics were used in reaching
; causal conclusions.
; Global variables:  all_events.
(setq all_events nil)
(defun make_event (temporal spatial descriptions)
   (let ((evnt (newsym 'event_)))
        (put evnt 'time temporal)
        (put evnt 'space spatial)
        (put evnt 'descriptions descriptions)
        (setq all_events (cons evnt all_events))
        (my_print '"Event made:")
        (print_plist evnt)
        evnt
   )
)
; ******************************************************
; data abstraction for events:
(defun event_time (evnt)
   (get evnt 'time)
)
(defun event_space (evnt)
   (get evnt 'space)
)
(defun event_start (evnt)
   (car (event_time evnt))
)
(defun event_end (evnt)
   (cadr (event_time evnt))
)
(defun x_coords (evnt)
   (car (event_space evnt))
)
(defun y_coords (evnt)
   (second (event_space evnt))
)
(defun z_coords (evnt)
   (third (event_space evnt))
)
 
(defun event_descriptions (evnt)
   (get evnt 'descriptions)
)
(defun event_causes (evnt)
   (get evnt 'causes)
)
(defun event_effects (evnt)
   (get evnt 'effects)
)

    
; *******************************************************
; SIMULTANEOUS determines that two events take place over exactly the 
; same time.
(defun simultaneous (ev1 ev2)
   (and (equal (event_start ev1) (event_start ev2))
        (equal (event_end ev1) (event_end ev2))
   )
)
; *******************************************************
; BEFORE returns true if e1 happened before e2.
(defun before (e1 e2)
   (and (< (event_start e1) (event_start e2))
        (<= (event_end e1) (event_end e2))
   )
)
; ********************************************************
; AFTER
(defun after (e1 e2)
   (and (> (event_start e1) (event_start e2))
        (>= (event_end e1) (event_end e2))
   )
)
; ********************************************************
; CONTIGUOUS:  two events are spacially contiguous if all their
; spatial coordinates intersect.
   
(defun contiguous (ev1 ev2)
   (and (overlap (x_coords ev1) (x_coords ev2))
        (overlap (y_coords ev1) (y_coords ev2))
        (overlap (z_coords ev1) (z_coords ev2))
   )
)
; ********************************************************
; OVERLAP is true if two sets of coordinates intersect.
(defun overlap (coords1 coords2)
   (or (num_between (car coords1) coords2)
       (num_between (cadr coords1) coords2)
   )
)
; *************************************************************
; NUM_BETWEEN:  a is between (b c) if b <= a <=c.
(defun num_between (num nums)
   (and (<= (car nums) num)
        (<= num (cadr nums))
   )
)
; **************************************************************
; HEUR1_BEFORE is a causal heuristic that says that if one event
; is before another, it might be the cause.
(defun heur1_before (ev1 ev2)
   (cond ( (before ev1 ev2)
           (my_print ev1 '" is before " ev2 '".  Value: " heur1_val)
           heur1_val
         )
         (t 0)
   )
)
; ********************************************************
; HEUR2_CONTIG says that contiguous events are more likely to be causally
; related.
(defun heur2_contig (ev1 ev2)
   (cond ( (contiguous ev1 ev2)
           (my_print ev1 '" is contiguous with" ev2 
                         '".  Value: " heur2_val)          
           heur2_val
         )
         (t 0)
   )
)
; ******************************************************
; HEUR3_COMMON checks for a common cause.
(defun heur3_common (ev1 ev2)
   (cond ( (common_cause ev1 ev2) 
           (my_print "Common cause found for " ev1 '" and " ev2)
	   0
         ) 
         (t heur3_val)
   )
)
; ******************************************************
; COMMON_CAUSE checks to see if two events have a common cause.
; A more thorough version of this would do a search to set up
; the event causes.
(defun common_cause (ev1 ev2)
   (intersect (event_causes ev1) (event_causes ev2))
)
; ******************************************************
; HEUR4_CHAIN looks to see if there is a chain of causal rules leading 
; from descriptions of one event to descriptions of another.
; chain_limit is a constant of how deep to search, i.e. how many
; inferences to allow in a chain.
(setq chain_limit 5)
(defun heur4_chain (ev1 ev2)
   (let ( (prob_name (newsym 'event_chain_prob_)))
        (make_problem prob_name 
                      (event_descriptions ev1)
                      (event_descriptions ev2)
                      'event_chain
        )
        (setq timesteps chain_limit)
        (solve_problem prob_name)
        ; were any goals (descriptions of ev2) satisfied?
        (cond ( goals_satisfied   ; see prob.l:  is_satisfied
                (my_print '"Causal chain found between " ev1 '" and " ev2)
                (my_print '"Descriptions satisfied:  "  goals_satisfied)
                heur4_val
              )
              (t heur4_neg_val)
        )
   )
)
; ******************************************************
; CAUSE? says whether e1 causes e2, using heuristics.
; Causal constants:  
(setq heur1_val 1)
(setq heur2_val 1)
(setq heur3_val 1)
(setq heur4_val 5)
(setq heur4_neg_val .5)
(setq cause_threshold .5)
(defun cause? (ev1 ev2)
   (let (cause_val)
        (setq cause_val
              (times (heur1_before ev1 ev2)
                     (heur2_contig ev1 ev2)
                     (heur3_common ev1 ev2)
                     (heur4_chain  ev1 ev2)
              )
        )
        (my_print '"Causal value: " cause_val)
        (cond ( (> cause_val cause_threshold) 
                (my_print ev1 '" causes " ev2)
                t
              )
              (t nil)
        )
   )
)
      
                
	   
	   
; ***************************************************************


; FILE:        common.l
; PURPOSE:     Running PI in common lisp.
; PROGRAMMER:  Paul Thagard.
; CREATED:     11-14-86.
; UPDATED:     12-18-86

; For conversion from Franz to Common:
(defun greaterp (num1 num2) (> num1 num2))
(defun lessp (num1 num2) (< num1 num2))
(defun plist (atm) (symbol-plist atm))
(defun quotient (num1 num2) (/ num1 num2))
 
(defun times (&rest arguments) (apply '* arguments))
(defun diff (num1 num2) (- num1 num2))
(defun add (&rest arguments) (apply '+ arguments))
(defun add1 (num) (+ 1 num))
(defun memberlist (lst1 lst2) (member lst1  lst2 :test 'equal)) ; otherwise uses eq
(defun subsetlist (lst1 lst2) (subsetp lst1 lst2 :test 'equal))
 
; *********************************************************
; For conversion from old Michigan lisp to Common:
(defun put (atm prop val) (setf (get atm prop) val))
(defun divide (num1 num2) (/ num1 num2))
 
(defun sub (num1 num2) (- num1 num2))
(defun intersect (lst1 lst2) (intersection lst1 lst2))
; *********************************************************
; For general conversion:
(defun my_max (num1 num2) (max num1 num2))
(defun subset (l1 l2) (subsetp l1 l2))
(defun remove_duplicates (lst) (remove-duplicates lst :test #'equal ))
; MY_PRINT prints out any number of arguments.
(defvar where_to_print *standard-output*)   ; optional output stream
(defun my_print (&rest arguments)
   (prog (args)
      (setq args arguments)
      loop
      (cond ( (null args) (terpri where_to_print) (return t)))
      (princ (car args) where_to_print)
      (setq args (cdr args))
      (go loop)
   )
)
; ***********************************************************
; For atom making (from Marie):
; CONCAT ; THIS DEPENDS ON STRING-APPEND, WHICH WAS ONLY
; IN SUN COMMON LISP.   REPLACE WITH PATCH AT TOP OF THIS PAGE.
;(defun concat (&rest concat-things)
  "Take any number of strings, atoms or numbers, smash them together,
;   (after making them all into strings) and return a symbol of the result."
;   (read-from-string (apply 'string-append 
;		           (mapcar 'coerce-string concat-things)))
;)
(defun coerce-string (thing)
  "Make a thing (number, symbol, string) into a string."
       (cond ((numberp thing)
              (prin1-to-string thing))
             ((symbolp thing)
              (symbol-name thing))
             ((stringp thing)
              thing))
)
;; BEGIN newsym functions (similar to gensym)
(defvar *NEWSYM-PREFIX* 'c)
(defun newsym (symb)
  "Given a symbol, get it's counter and create a new symbol consisting
   of the symbol concat'ed with its number.  If symbol is nil, use 
   the current value of *NEWSYM-PREFIX*"
   (cond ((symbolp symb)
          (if (null symb) (setq symb *NEWSYM-PREFIX*))
          (let (count)
               (if (null (get symb '*newsym-counter*))
                   (setf (get symb '*newsym-counter*) 0))
               (setf (get symb '*newsym-counter*)
                     (1+ (setq count (get symb '*newsym-counter*))))
               (concat symb count)))
         (t (princ "Error: non-symbol arg to newsym ")
            (princ symb))))
; **********************************************************
; ATOM_BEGINS checks to see whether an atom begins with a
; given character.
(defun atom_begins (atm char)
   (and (atom atm)  (eq (aref (coerce-string atm) 0) char))
)

; ATOM_INCLUDES checks to see whether an atom includes a given
; character.
(defun atom_includes (atm char)
   (prog (str index)
      (setq str (symbol-name atm))
      (setq index 0)
      loop
      (if (> (+ 1 index) (length str)) (return nil))
      (if (equal (aref str index) char) (return t))
      (setq index (+ 1 index))
      (go loop)
   )
)
         
; ************************************************************


; ************************************************************
; For convenience:
(defun q () (quit))
(defun exit () (quit))
(defun unix (str) (run-unix-program str))
(defun lv+ () (setq *load-verbose* t))
(defun lv- () (setq *load-verbose* nil))

; ***************************************************************
; For more informative printing:
(setq *print-level* 20)
(setq *debug-print-level* 20)
(setq *print-length* 100)
(setq *debug-print-length* 100)

;  FILE         concepts.l
;  PROGRAMMER:  Paul Thagard
;  PURPOSE:     Concept formation, both from rules and by combination
;  CREATED:     5-22-84
;  LAST UPDATE: 5-5-87
 
; ********************************************************
;       Bottom-up concept formation 
;  *******************************************************
; RULES_WITH_SAME_CONDN finds all pairs of rules that have the
; same 2 or more conditions; returns a list of pairs.
(defun rules_with_same_condn (rule_list)
   (prog (rules rul rest_of_rules result)
      (setq rules rule_list)
      (setq result nil)
;     for each rule, check against rest of rules:
      loop1
      (cond ( (null rules) (return result) ))
      (setq rul (car rules))
      (setq rest_of_rules (cdr rules))
;        check against each remaining rule:
         loop2
         (cond  ( (null rest_of_rules)
                  (setq rules (cdr rules))
                  (go loop1)
                )
         )
;        see if 2 rules have same conditions:
         (cond ( (and (greaterp (length (get rul 'conditions)) 2)
                      (equal (get rul 'conditions)
                             (get (car rest_of_rules) 'conditions )
                      )
                 )
                 (setq result (cons (list rul (car rest_of_rules))
                                    result
                              )
                 )
               )
         )
         (setq rest_of_rules (cdr rest_of_rules))
         (go loop2)
   )
)
; **************************************************************
; FORM_CONCEPT_FROM_RULES produces a new concept from 2 rules with
; the same conditions, attaching to the new concept a new set of rules.
; note:  limited to forming unary concepts.
(defun form_concept_from_rules (list_of_two_rules)
 (prog (start_concs new_conc rule_1 rule_2)
    (setq rule_1 (car list_of_two_rules))
    (setq rule_2 (second list_of_two_rules))
;   create the new concept:
    (setq start_concs (concepts_from (get rule_1 'conditions) ))
    (setq new_conc (make_name start_concs) )
    (cond ( (null (make_concept new_conc
                                '(thing)
                                '(thing)
                                nil
                                 nil
                                 .5     ;arbitrary starting activation
                  )
            )
            (return nil)      ; terminate if concept already exists
          )
     )
;  activate new concept:
   (setq active_concepts (cons new_conc active_concepts))
;  make rules relating old and new concepts:
;  1.  old -> new
   (make_rule_long new_conc
                   (get rule_1 'conditions)
                   (list (list new_conc '($x) 'true 'deduce) )
                   '???
                   'default
                   .2        ; arbitrary weak strength
   )
;  2.  new -> old
   (make_rule_long new_conc
                   (list (list new_conc '($x) 'true ) )
                   (get rule_1 'conditions)
                   '???
                   'default
                   .2        ; arbitrary weak strength
   )
 )
)
;  *****************************************************************
;         Conceptual combination.
;  ***************************************************************** 
;  COMBINE (concept1 concept2) performs conceptual combination on
;  the two concepts, producing a new one.
;   
(defun combine (concept1 concept2)
   (let (newconc new_concept_made)  
        (cond ( (and (name_not_in concept1 concept2)
                     (conflicting (get concept1 'rules)
                                  (get concept2 'rules)
                     )
                 )   
                 ; form new concept if originals conflict
                (setq newconc (concat concept1 '_ concept2))
                (setq new_concept_made
                      (make_concept newconc    ; new name
                        (list concept1 concept2)
                        nil                     
                        (make_messages newconc
                                       (common_inst concept1 
                                                    concept2
                                       )
                        )
                         nil                    
                         (min (get concept1 'activation) 
                              (get concept2 'activation)
                         )
                    )
               )
               (cond ( new_concept_made
                      (my_print  '"Conceptual combination producing: " newconc)
                      (setq active_concepts (cons newconc active_concepts)) 
                      (build_all_rules newconc concept1 concept2)   ; add rules
                     )
               )
             )
          )
   new_concept_made  ; return name of concept if one was made
   )
)   
; ADD:  make rules for superordinates when this is appropriate.  E.g. 
;       sound_wave -> wave.  Note this shouldn't apply to apartment_dog.
; This depends on kind of reconciliation required. 
 
;  ***********************************************************
; CONFLICTING checks to see if two concepts have any rules which
; would generate conflicting expectations.  e.g.  feminist and bank
; teller conflict, but bank teller and short do not.
; <<This should be more complicated:  conflict should require not
; only having rules in the same slot, but also a check for 
; conflicting values.  E.g. reflects and propagates can both
; be in a motion slot without conflict.  Need semantic 
; inconsistency.>> 
(defun conflicting (rules1 rules2)
    (cond ( (null rules1) nil)
          ( (and (not_member (get (car rules1) 'slot) 
                             '(subordinate superordinate)
                 )
                 (member (get (car rules1) 'slot)
                         (mapcar '(lambda (rul)
                                      (get rul 'slot)
                                  )
                                  rules2
                         )
                  )
             )
             (list '"Conflict: " (car rules1) )
          )
          (t (conflicting (cdr rules1) rules2))
     )
)
;  ***********************************************************
;  NAME_NOT_IN checks for redundant combinations, e.g. striped and
;  striped_apple.
;  kluge:  prevents combinations of more than two base-concepts.
;          - conflict checking should take care of this.
;  Also prevents redundancy of A_B and B_A.
(defun name_not_in (name1 name2)
    (and  (not (atom_includes name1 #\_ ))
          (not (atom_includes name2 #\_ ))
          (null (member (concat name2 '_ name1) all_concepts))
    )
)
 
; ************************************************************
;  MAKE_MESSAGES creates messages.
(defun make_messages (newconc args)
   (prog (insts result)
      (setq insts args)
      (setq result nil)
      loop
      (cond ( (null insts) (return result)))
      (setq result 
            (cons (list newconc (list (car insts)) 'true .5)
                  result
            )
      )
      (setq insts (cdr insts))
      (go loop)
   )
)
;  ***********************************************************
 
;  BUILD_ALL_RULES (newconcept concept1 concept2) creates rules for
;  newconcept using the rules from the other two concepts.
 
(defun build_all_rules (newconcept concept1 concept2)
   (prog (c1_rules)
         (setq c1_rules (get concept1 'rules))
         loop
         (cond ((null c1_rules) (return '"done combining.") ))
         (build_one_rule newconcept
                          (car c1_rules)
                          (get concept2 'rules)
         )
         (setq c1_rules (cdr c1_rules))
         (go loop)
   )
)
 
 
 
;  ***********************************************************
 
;  BUILD_ONE_RULE (newconcept rule rulelist) builds rules for newconcept
;  using the single rule rule taken from concept1 and the rulelist taken
;  from concept2.  If the rulelist contains conflicting slots, then
;  reconcile must be called to decide what the resulting rule must look
;  like.  New rules are formed only when reconciliation was necessary, since
;  otherwise the inferences go through anyway by virtue of superordinate 
;  rules.  
 
(defun build_one_rule (newconcept rule rulelist)
   (prog (c2_rules)
         (setq c2_rules rulelist)
         loop
         (cond ( (null c2_rules)
                 (return '"no slot conflicts")
               )
          )
          (cond ( (equal (get rule 'slot)
                         (get (car c2_rules) 'slot)
                  )
                  (reconcile newconcept rule (car c2_rules))
                  (return '"slot conflicts reconciled")
                )
          )
          (setq c2_rules (cdr c2_rules))
          (go loop)
   )
)
 
;  ************************************************************
 
;  assorted junk:
 
(defun pred_super (rule)
   (car (get (get_pred_r rule) 'superordinates))
)
 
(defun get_pred_r (rule)
   (car (car (get rule 'conditions)))
)
 
;
(defun isactual (rule1)
     (equal 'actual (get rule1 'status))
)
(defun isdefault (rule1)
      (equal 'default (get rule1 'status))
)
;  ************************************************************
;  RECONCILE produces a new rule from two conflicting ones.
;  global variables:  invar_r1, invar_r2, winner
(defun reconcile (newconcept rule1 rule2)
    (setq invar_r1 (invar (pred_super  rule1 )
                          (get rule1 'slot)
                   )
          invar_r2 (invar  (pred_super rule2)
                           (get rule2 'slot)
                   )
    )
    ; pick actual value over default
    (cond ( (and (isactual rule1)               
                 (isdefault rule2)
            )
            (setq winner rule1)
          )
          ( (and (isactual rule2)
                 (isdefault rule1)
            )
            (setq winner rule2)
          )
    
   ; pick most invariable
          ( (greaterp invar_r1 invar_r2)        
            (setq winner rule1)
          )
          ( (lessp invar_r1 invar_r2)
            (setq winner rule2)
          )
   ; decide on basis of property of common instance
          ( (setq winner (instance_decides (get_pred_r rule1)
                                           (get_pred_r rule2)
                                           rule1
                                           rule2
                         )
            )
            winner
          )
   ; default:  go with strongest rule - cruder measure of variability
          ( (greaterp (get rule1 'strength) (get rule2 'strength))
            (setq winner rule1)
          )
          (t (setq winner rule2) )
    )
;  add:  other rules for reconciliation, especially problem solving.
 
    (make_rule newconcept
               newconcept
               (caar (get winner 'actions))     ; not general
               (get winner 'slot)
               'default
               (divide (get winner 'strength) 1.5)
    )
)
 
;  ************************************************************
 
; INVAR calculates invariability
; by dividing the number of subkinds of kind1 about which it has information
; concerning kind2 by the total number of values of kind2 those subkinds
; possess.  this is not intended to be optimal, but gives a rough
; approximation to what people do.
 
;
(defun invar (kind1 kind2)
   (prog (range varieties subkinds count)
         (cond ( (or (null kind1) (null kind2))  ; no kinds
                 (return 1)                     ; high default value
               )
         )
         (setq  range 0
                varieties 0
                subkinds (get kind1 'subordinates)
                count 0
         )
         loop
         (cond ( (null subkinds)             ;  no subkinds
                 (cond ( (zerop varieties)
                         (return .1)         ; low default value
                       )
                       (t (return (divide range varieties)))
                  )
                )
         )
         (setq count (countrules (car subkinds) kind2))
         (cond ( (greaterp count 0)
                 (setq range (add1 range))
               )
         )
         (setq varieties (add varieties count))
         (setq subkinds (cdr subkinds))
         (go loop)
   )
)
;  ************************************************************
 
;  COUNTRULES counts the number of rules that a concept has with a
;  a given slotname.  thus if parrots have two rules concerning color
;  countrules returns 2.
 
(defun countrules (concept slotname)
   (prog (rulelist result)
         (setq rulelist  (get concept 'rules)
               result 0
         )
         loop
         (cond ( (null rulelist) (return result)))
         (cond ( (equal (get (car rulelist) 'slot) slotname )
                 (setq result (add1 result))
               )
         )
         (setq rulelist (cdr rulelist))
         (go loop)
    )
)
;  ************************************************************
;  INSTANCE_DECIDES attempts reconciliation on the basis of what
;  instances two concepts have incommon.  If C1 and C2 have a
;  common instance with a property predicted by rule 1, then 
;  rule 1 is the winner.
(defun instance_decides (conc1 conc2 rule1 rule2)
   (prog (common_inst first_inst)
      (setq examples (common_inst conc1 conc2))
      loop
      (cond ( (null examples ) (return nil)))
      (setq first_inst (car examples))
      (cond ( (equal (get first_inst (get rule1 'slot))
                     (caar (get rule1 'actions))
              )
              (return rule1)
            )
            ( (equal (get first_inst (get rule1 'slot))
                     (caar (get rule2 'actions))
              )
              (return rule2)
            )
      )
      (setq examples (cdr examples))
      (go loop)
   )
)
; ********************************************************
; COMMON_INST returns the names of instances common to two concepts.
; Cf. getinstances, common, and common1 in gen.l.
; This works only for unary predicates.
(defun common_inst (conc1 conc2)
   (intersect (instances_from2 conc1)  ;cf gen.l
              (instances_from2 conc2)
   )
)
; 
(defun instances_from2 (conc)
   (mapcar 'first_arg (get conc 'instances))
)
;
(defun first_arg (mess) 
    (car (second mess))
)
; ****************************************************************
;     Full conceptual combination:  4-87
;       - includes explanation-based.
; ***************************************************************
; FULL_COMBINE does a full range of kinds of conceptual combination:
;   - disjunctive
;   - conjunctive - role-modifying
;                 - intersective - structure-based
;                                - explanation-based
;   mode is: conjoin, disjoin                            
; 
(defun full_combine (conc1 conc2 mode)
    ; disjunctive?
    (if (equal mode 'disjoin) (combine_dis conc1 conc2)
        ; otherwise conjoin:
        ; do concepts intersect?
        (if (common_inst conc1 conc2) (intersect_combine conc1 conc2)
            ; otherwise, do role-modification:
            (role_mod_combine conc1 conc2)
        )
    )
)
; *****************************************************************
; INTERSECT_COMBINE does conceptual combination when two concepts have
; an instance in common.  It does a structural combination (as in old
; version of PI and also does explanation-based.
(defun intersect_combine (conc1 conc2)
   (let (new_conc)
        (setq new_conc (combine conc1 conc2)) ; structural combination
	(if new_conc (explain_combine new_conc conc1 conc2))
   )
)
; ****************************************************************
; EXPLAIN_COMBINE adds features to a combined concept based on what it
; takes to explain how, given one feature, the other is possible.
(defun explain_combine (combined_conc conc1 conc2)
   (let (start_conc explain_conc hypotheses)
        ; select the more salient concept as what is to be explained.
        (if (more_salient conc1 conc2)
            (and (setq explain_conc conc1)
                 (setq start_conc conc2)
            )
            ; else
            (and (setq explain_conc conc2)
                 (setq start_conc conc1)
            )
        )
        ; do an explanation:
        (setq hypotheses (chain_explain start_conc explain_conc))
        ; convert hypotheses found into properties of new concept:
        (if hypotheses (add_hyp_rules combined_conc hypotheses 
                                      start_conc explain_conc
                       )
        )
   )
)
; ****************************************************************
; MORE_SALIENT should be determined by context.  Here use state of 
; activation as a stand-in.
(defun more_salient (conc1 conc2)
   (> (get conc1 'activation) (get conc2 'activation))
)
; ****************************************************************
; CHAIN_EXPLAIN is like explain, except that when abduction forms
; a new hypothesis, the hypothesis is added to the list of goals to
; be explained, until a hypothesis is reached that corresponds to
; where the explanation was intended to begin.
; global variables:  chain_explain_flag, conc_to_explain_with
; Returns a list of hypotheses formed during the chaining.
; Should quit when conc1 is involved in a hypothesis.
(defun chain_explain (conc1 conc2)
   (let (old_hypoths)
        (setq chain_explain_flag t)
        (setq conc_to_explain_with conc1)
        (setq old_hypoths (get 'all_hypothesis 'members))
        (explain 'fact
                 (list (make_condition conc1))
                 (list (make_condition conc2))
        )
        ; turn off constants:
        (setq chain_explain_flag nil)
        (setq conc_to_explain_with nil)
        (setq stop_problem nil)
        ; return new hypotheses
        (set-difference (get 'all_hypothesis 'members)
                        old_hypoths
        ) ; returned
   )
)
; ****************************************************************
; ADD_HYP_RULES turns hypotheses H into rules C -> H attached to
; concept C.  Hypotheses must have been part of the explanatory chain
; from the starting concept to the goal concept.
(defun add_hyp_rules (conc hypoths start_conc explain_conc)
   (my_print '"Adding to " conc '" using " hypoths)
   (prog (hyps hyp chain_of_hyps)
      (setq hyps hypoths)
      (setq chain_of_hyps (trace_expln_chain 
                                (find_mess_name start_conc 
                                                (get 'all_hypothesis 'members)
                                )
                                (find_mess_name explain_conc 
                                                (get 'all_explanandum 'members)
                                )						
                           )
      )
      loop
      (if (null hyps) (return 'ADD_HYP_DONE))
      (setq hyp (car hyps))
      (if (part_of_expln hyp chain_of_hyps)
          (make_rule conc conc 
                    (car (get hyp 'message))
                    ; slot determined by kind:
                    (car (get (car (get hyp 'message)) 'superordinates))
                    'default
                    .1
          )
      )
      (setq hyps (cdr hyps))
      (go loop)
   )
)
; ****************************************************************
; TRACE_EXPLN_CHAIN lists those hypotheses that played a direct role in
; a chain of explanations. Does depth-first search.  Returns whole path.
; Note:  will not get second path which might exist.
(defun trace_expln_chain (start_hyp explanandum)
   (prog (queue expansion)
      (setq queue (list (list start_hyp)))
      loop
      (cond ( (null queue) (return nil))
            ( (equal explanandum (caar queue))
              (return (reverse (car queue)))
            )
      )
      (setq expansion (expand_expln_chain (car queue)))
      (setq queue (cdr queue))
      (setq queue (append expansion queue))
      (go loop)
   )
)
; ***************************************************************
; EXPAND_EXPLN_CHAIN adds new possible paths.
(defun expand_expln_chain (hyp_path)
   (mapcar #'(lambda (hyp)
                (cons hyp hyp_path)
             )
           (get (car hyp_path) 'explains)
   )
)
; ***************************************************************
; FIND_MESS_NAME finds the name of a message having the given concept
; as predicate.  
(defun find_mess_name (conc mess_list)
   (prog (messages answer)
      (setq messages (mapcar #'(lambda (mess)
                                  (get mess 'message)
                               )
                               mess_list
                      )
      )
      (setq answer nil)
      loop
      (cond ( (null messages)
              (if (> (length answer) 1)
                  (my_print '"WARNING:  find_mess_name finds more than one hypothesis: " answer)
              )
              (return (if (null answer) nil
                          (fifth (car answer))
                      )
              )
            )
      )
      (if (equal (caar messages) conc)
          (setq answer (cons (car messages) answer))
      )
      (setq messages (cdr messages))
      (go loop)
   )
)
      
; ******************************************************
; PART_OF_EXPLN determines if a hypothesis played a role in an
; explanation chain, either as a step or as a co-hypothesis.
(defun part_of_expln (hypoth chain_of_hypoth)
   (or (member hypoth chain_of_hypoth)
       (member hypoth 
               (union_map #'(lambda (hyp)
                                (get hyp 'co_hypotheses)
                            )
                           chain_of_hypoth      
               )
        )
   )
)			       

			       


; end of concepts.l
 



; FILE:         explain.l
; PROGRAMMER:   Paul Thagard
; PURPOSE:      Explanation and abduction in PI.
; CREATED:      8-7-84
; LAST UPDATED: 1-18-89
; ********************************************************
; EXPLAIN treats explanation as a species of problem solving.  A
; fact is explained by treating it as a goal to be reached.  A rule
; is explained by treating its conditions as starting points and its
; action as a goal.  In the first case, the explanandum is a list of messages;
; in the second, it is a rule name.
;
(defun explain (type context explanandum)
   (my_print '"-----------------------------------------------")
   (my_print '"explaining " explanandum)
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
         (t (my_print '"explanation error."))
     )
    (make_problem prob_name start_list goal_list 'explanandum)
    (put prob_name 'explan_status 'explanation)
    (setq e_result (solve_problem prob_name))      ; solve the problem
    (cond ( e_result (my_print explanandum '" explained.")
                     ; if any rule was explained by an abductive
                     ; generalization, invoke theory evaluation (theory.l).
                     (cond ( (get prob_name 'abduc_gens)
                             (store_all_explns (get prob_name 'abduc_gens)
                                               explanandum
                             )
                           )
                      )
          )
                             
		     
          (t (my_print '"No explanation found for " explanandum))
    )
)
; **************************************************
; STORE_ALL_EXPLNS notes what abductively generalized rules
; played a role in explaining a rule.
(defun store_all_explns (rule_list rul)
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
(defun trig_abduce ()
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
; Given rule A,B,C --> E, with E to be explained, A, B, and C are
; hypothesized.  
; Works on triple: (<explanandum> <rule>
; <conditions>).  Returns a list of names of hypotheses.
; <<Major flaw:  check for consistency of hyptotheses is 
;   purely syntactc; will not catch semantic inconsistencies
;   such as x is green and red.>>
(defun abduce_condns (triple)
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
(defun all_bound_vbls (mess_list)
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
(defun abd_contradict (condn_lst mess_list)
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
(defun mess_contra (mess mess_lst)
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
(defun truth_contra (val1 val2)
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
(defun record_dependencies (hyp_list)
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
(defun abduce_fact (explanandum rul condn abd_type)
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
                  (my_print '"Supplementary abduction of " new_mess) 
                  (my_print '"    from " explanandum '" and " rul) 
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
; <<Careful:  sometimes by a hypothesis I means its name, sometimes
;             its message.>>
; Here hyp is a message.
(defun make_hypothesis (hyp explanandum rul abd_type)
   (setq hyp (name_message hyp 'hypothesis))
   (cond ( (atom explanandum) ; want message
           (setq explanandum (get explanandum 'message)) 
         )
   )
   (my_print abd_type  '" abduction of "  hyp)
   (my_print '"    from "  explanandum  '" and "  rul )
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
; (<explanandum> <explaining rule> <condn to abduce>).
 
(defun find_abductions (explananda rule_list)
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
; Returns triple of form (<explanandum> <rule> <condition-list>).
; Note:  won't work for rules with multiple actions.
(defun find_explns (explanandum rule_list)
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
;  <<OBSOLETE>>
;  ALL_BUT_ONE (rule) checks to see if all but one condition of the
;  rule is an active message.  if so, it returns that member.  the role of this
;  function in abduction is to find one condition of a potentially
;  explaining rule which is not on the message list; that condition is then
;  abduced.  this function returns a pair: (<rule> <condition>)
 
(defun all_but_one (rul)
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
(defun not_abduced (hyp explanandum rul)
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
(defun second_first (lst) (second (car lst)))
; *********************************************************
;        ABDUCTIVE GENERALIZATION
; *********************************************************
; TRIG_ABD_GEN is called by trigger in trig.l.  It looks 
; through the list of active messages for general hypotheses, e.g.
; H(x), that have played a role in explaining why G(x), given that 
; F(x).  It then forms the rule: Fx -> Hx.  Forms rules with any number
; of conditions and can handle relations, too.
(defun trig_abd_gen ()
   (mapcar 'build_abd_gen (find_gen_hypoth active_messages))
)
; **************************************************************
; FIND_GEN_HYPOTH finds messages that are hypotheses using general variables.
(defun find_gen_hypoth (mess_lst)
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
(defun contains_gen_vbl (arg_lst)
    (cond ( (null arg_lst) nil)
          ( (atom_begins (car arg_lst) #\$) t)
          ( t (contains_gen_vbl (cdr arg_lst)))
    )
)
; ******************************************************************
; BUILD_ABD_GEN forms a general rule from the general hypothesis, looking
; for starting conditions with the same variables as the hypothesis.
; global variable:  abd_rule_made
(defun build_abd_gen (hyp_mess)
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
            (my_print '"Abductive generalization formed from " hyp_mess)
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
(defun mess_with_vbl (arg_lst mess_lst)
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
(defun un_project_truth_val (val)
    (if (equal val 'proj_true) 'true 'false)
)

; For ANALOGICAL ABDUCTION, see analog.l.
; end of EXPLAIN.L 


;  FILE:        franz.l
;  PROGRAMMER:  Paul Thagard
;  PURPOSE:     Miscellaneous functions for running PI in Franzlisp.
;  CREATED:     9-9-85
;  LAST UPDATE: 10-22-85
; ************************************************
;  to speed up working in Franz:
(defun b () (baktrace))
(defun s () (showstack))
(defun bs () (baktrace) (showstack))
(defun e () (exit))
(defun r () (reset))
(defun pf () (setq print_to_file nil))
(defun pt () (setq print_to_file t))
; ************************************************
; PUT is just like putprop except it reverses the
; order of the second two parameters:
; put on the atom atm under the property prop the value
(defun put (atm prop value)
   (putprop atm value prop)
)
; ************************************************
 
(defun loadall ()
   (load 'junk 'pi.new)
)
; **************************************************
; UNION gives the union of two lists, removing duplicates
(defun union (lst1 lst2)
   (remove_duplicates (append lst1 lst2))
)
; **********************************************************
; INTERSECT gives the intersection of two lists
(defun intersect (lst1 lst2)
    (prog (lst result)
       (setq lst lst1)
       (setq result nil)
       loop
       (cond ( (null lst) (return (reverse result)) ) )
       (cond ( (member (car lst) lst2)
               (setq result (cons (car lst) result))
             )
       )
       (setq lst (cdr lst))
       (go loop)
    )
)
; ****************************************************************;
(defun clear_out ()
;  optional output file
   (setq out_port (outfile 'lispout))
)
(setq out_port (outfile 'lispout))
;  MY_PRINT prints out any number of items.
 
(defun my_print arguments
   (prog (count)
       (setq count 1)
       loop
       (cond ( (greaterp count arguments)
               (cond ( print_to_file (terpri out_port))
                     ( t (terpri))
	       )	     
               (return nil)
             )
             (t (cond ( print_to_file (princ (arg count) out_port))
                      ( t (princ (arg count)))
		)
	     )
       )  
       (setq count (add1 count))
       (go loop)
   )
)
;  ***********************************************
;  exclude (list1 list2) returns a list consisting of list2 with
;  all the elements of list1 removed.
(defun exclude (list1 list2)
    (cond ( (null list1) list2)
          ( t (exclude (cdr list1)
                        (remove (car list1) list2)
	      )
	    
	  )
    )
)
; *******************************************************************
;  division:
(defun divide (num1 num2)
    (quotient num1 num2)
)
; *******************************************************************
;  subtraction:
(defun sub (num1 num2)
   (diff num1 num2)
)
; ********************************************************************
;  
;  end pi.mis.franz.l












    
; FILE:          gen.l
; PROGRAMMER:    Paul Thagard
; PURPOSE:       Generalization and specialization
; CREATED:       5-22-84
; LAST UPDATE:   12-19-86  ; 1-19-89
; **********************************************
; somewhat arbitrary constants:
(setq gen_threshold .5)        ; minimum strength for generalization
(setq max_instances 20)        ; maximum number of instances
; *********************************************
 
; GENERALIZE constructs synchronic rules by generalization,
; setting the strength of the rule on the basis of number
; of instances and variability.
;
(defun generalize (triple)
   (setq class (car triple)
         property (second triple)
         vbl_status (third triple)
   )
   (setq invar_result (invar (car (get class 'superordinates))
                             (car (get property 'superordinates))
                      )
   )
   (setq common_instances (length (common class property)))
   (setq stren (times (divide common_instances
                              max_instances
                      )
                      invar_result
               )
   )
   (cond ( (and (greaterp stren gen_threshold)        ; strong enough
                (null (check class property))        ; check for counterexampl
           )
           (setq gen_result
                 (make_rule class class property     ; redundant?
                            (get property 'superordinates)
                            'default stren
                 )
           )
         )
         (t (setq gen_result nil))
   )
   (cond  ( (and gen_result trace_prob)
            (my_print class '" --> " property
                      '" generalized from "
                      common_instances
                      '" instances."
            )
          )
          
    )
   
)
; note:  for invar see file concepts
; *********************************************
;  CHECK checks for counterexamples, i.e. instances of a class which
;  lack a property.
;  alogorithm:  for all instances of class, for all instances of property
;  return nil if there is an instance of class which is not an instance
;  of property. (2 ways: typicality > 0 vs. 0, or just not listed).
;   failures to check should trigger refutation or specialization.
;   confirmations should add to strength of rule.
; see below, near end of file.
; *********************************************
;
; GETINSTANCES returns a list of the instances of a class.  Note
; that it gets subordinates' instances as well..
 
(defun getinstances (class)
  (prog (file result)
    (setq file    (cons class (get class 'subordinates))
          result  nil
    )
    loop
    (cond ((null file) (return result)))
    (setq result (union result
                        (instances_from (car file))
                 )
    )
    (setq file (cdr file))
    (go loop)
  )
)
; *******************************************************
;  INSTANCES_FROM extracts the arguments from a list of instances
;  in the form of messages:  e.g. in the message (black ($x) true)
;  it extracts ($x).
(defun instances_from (concpt)
   (union_map 'get_argument
              (get concpt 'instances)
   )
) 
; *******************************************************
;
; GETSUBKINDS lists the subkinds of a class:
 
(defun getsubkinds (class)
  (prog (this open result)
    (setq result    nil
          open      (list class))
    loop
    (cond ((null open) (return result)))
    (setq this (car open))
    (cond ( (get this 'subordinates)
          ; then:
            (setq open (union open (get this 'subordinates)))
            (setq result (union result (fget this 'subkinds 'range)))
          )
    )
    (setq open (remove this open))
    (go loop)
  )
)
;
; ************************************************************
; COMMON gets the common instances of two classes.
;
; an easy but psychologically implausible way of getting the common
; instances of two properties would be:
;
 
(defun common (class1 class2)
  (intersection (getinstances class1)
                (getinstances class2)) )
 
; this is implausible <???>
; since you may not have accessible e.g. all blue things.
; perhaps classes like bird have locatable instances, but not properties.
; hence the function common should function to find the common instances
; of a class and a property by checking each instance of the class
; to see if it has the property:
 
 
(defun common1 (class property)
   (prog (file result)
     (setq result nil
           file   (getinstances class))
     loop
     (cond ((null file)  (return result)))
     (cond ((is? (car file) property)
            (setq result (cons (car file) result)) ))
     (setq file (cdr file))
     (go loop) ))
;
 
;  ********************************************************
;  IS? checks whether a thing has a property
 
(defun is? (thing property)
  (equal property (get thing
                       (car (get property 'superordinates))
                  )
  )
)
 
; *********************************************************
;  )
;**********************************************************
; GEN_LONG is a more flexible version of generalize in that
; it can handle multiple conditions and n-ary predicates.
; example: (loves ($x $y)) (nice ($x))   ->  (loves ($y $x)).
; i.e.  if you love someone and you are nice, then the one
; you love loves you.  in the following definition, cond_list
; is a list of the instances from which generalization is being
; made, e.g. ((loves (mary john)) (nice (mary)) ) and act_list
; is the list of instances from which actions are formed, e.g.
; ( (loves (john mary)) )
;  gen_long now takes one argument, a list consisting of two lists,
;  the first a list of potential condtions, the second a list
;  of potential actions.  this is triggered by trig in pi.trig,
;  but only for simple cases.
;
(defun gen_long (list_of_two_lists)
   (setq cond_list (car list_of_two_lists))
   (setq act_list (second list_of_two_lists))  ; global variables: fix
   (setq vbl_lst univ_vbls)  ; univ_vbls set by begin.l
   (mapcar 'clear_vbls (union cond_list act_list) ) ;  remove old vbls
 
   (make_rule_long  (caar cond_list)      ; attach rule to concept
                    (mapcar 'fix_vbls cond_list)   ; conditions
                    (mapcar 'fix_action act_list)  ; actions
                    'anyslot                       ; arbitrary slotname
                    'actual
                    .5
    )
)
; ********************************************************************
; CLEAR_VBLS ensures that old associations of names with variables are cleared.
 
(defun clear_vbls (inst)
   (mapcar '(lambda (arg)
                (put arg 'variable nil)
            )
            (second inst)
   )
)
; ********************************************************************
; FIX_VBLS associates a variable with each argument in an instance,
; returning the instance with variables replacing names.  thus
; fix_vbls (loves (john mary)) returns (loves ($x $y)), with $x on
; the property list of john under the property variable.
;
(defun fix_vbls (instance)
   (prog (args result)
      (setq args (second instance))
      (setq result nil)
      loop
      (cond ((null args)
             (return (list (car instance) (reverse result)))
            )
      )
      (cond ((null (get (car args) 'variable))
             (put (car args) 'variable (car vbl_lst))
             (setq vbl_lst (cdr vbl_lst))
            )
      )
      (setq result (cons (get (car args) 'variable) result))
      (setq args (cdr args))
      (go loop)
   )
)
;***********************************************************
;
; FIX_ACTION uses the variable bindings set up by fix_vbls
; to set up an action, e.g. going from (loves (john mary))
; to (loves ($x $y)), where $x was previously associate with
; john.
 
(defun fix_action (instance)
   (prog (result args)
       (setq result nil)
       (setq args (second instance))
       loop
       (cond ((null args) (return (list (car instance)
                                        (reverse result)
                                   )
                           )
              )
        )
        (setq result (cons (get (car args) 'variable) result))
        (setq args (cdr args))
        (go loop)
   )
)
;*********************************************************
; samples (commented out)  these will no longer work because gen_long now takes a list of two lists.
; (setq trace_data t)
; (setq all_rules nil)
; (gen_long '( (loves (mary john)) (nice (mary)) )
;           '( (loves (john mary)) (nice (john)) )
; )
; (gen_long '( (owes (fred john five)) (worries (john)) ) '((hates (john fred))))
; *********************************************************
;  functions for specialiation:
; *********************************************************
; CHECK checks for counterexamples to a potential or existing
; generalization, returning the name of a counterinstance.
; note: what is returned is a list, e.g. (obj_a) or (obj_a obj_b).
;
(defun check (prop1 prop2)
   (prog (instances first_inst)
         (setq instances (instances_from prop1))
         loop
         (cond ( (null instances) (return nil) )) ; no counterexamples
         (setq first_inst (car instances))
         ; is the instance of p1 not an instance of p2?
         (cond ( (member first_inst (get_instances prop2 'false))
                 (trig_spec prop1 prop2 first_inst)  ; specialize?
                 (return first_inst)
               )
         )
         (setq instances (cdr instances))
         (go loop)
    )
)
; *********************************************************
; GET_INSTANCES gives a list of those instances known to have or not to
; have a property.   only works for unary predicates.
;
(defun get_instances (prop truth_val)
   (prog (messages first_mess result)
         (setq messages (get prop 'instances))
         (setq result nil)
         loop
         (cond ( (null messages)
                 (cond ( result                    ; unary kluge
                         (setq result (mapcar 'car result))
                       )
                 )
                 (return result)
               )
          )
         (setq first_mess (car messages))
         (cond ( (equal (third first_mess) truth_val)
                 (setq result (cons (second first_mess) result))
               )
         )
         (setq messages (cdr messages))
         (go loop)
    )
)
;**********************************************************
; TRIG_SPEC triggers specialization.  if check finds a counterexample
; to a rule that exists, then a specialized version of that rule
; should be formed.  e.g. from a-->b to a&c-->b.
;
(defun trig_spec (prop1 prop2 inst)
    (prog (bad_rule)
          (setq bad_rule (find_rule prop1 prop2) )
          (cond ( (and bad_rule
                       (greaterp (get bad_rule 'strength)
                                confidence_threshold
                       )
                   )
                   (spec prop1 prop2 inst bad_rule )
                )
          )
    )
)
; *********************************************************
; FIND_RULE looks for the existence of a rule a->b.
; it checks the list of rules attached to the concept a.
; returns name of the found rule. limited to simple rule.
(defun find_rule (prop1 prop2)
    (prog (ruls rul)
          (setq ruls (get prop1 'rules))
          loop
          (cond ( (null ruls)  (return nil) ))
          (setq rul (car ruls))
          (cond ( (equal (caar (get rul 'actions)) prop2)
                  (return rul)
                )
          )
    )
)
; **********************************************************
; SPEC specializes an existing rule using an unusualness principle.
; if the generalization a-->b fails with the counterinstance c,
; then we look for something unusual about c.  these can either be
; a property of c that all a's lack, or a property of all a's that
; c lacks.  in the former case, we want to specialize a&~p-->b.
; in the latter, a&p-->b.   limited to unary predicates.
; global variable: weird: the unusual condition.
;
(defun spec (prop1 prop2 inst old_rul)
   (setq  weird (unusual prop1 prop2 inst))
   (cond ( weird
           (make_rule_long  prop1
                            (list (make_condition prop1)  ; new conditions
                                  weird
                            )
                            (list (make_action prop2))
                            (get old_rul 'slot)
                            'default
                            (get old_rul 'strength)
            )
          )
   )
   (car all_rules)     ; return name of rule just made
)
; *********************************************************
; UNUSUAL finds something unusual about an instance c with respect
; to property a, a respect in which c is not like other a's.
(defun unusual (prop1 prop2 inst)
    (or (prop_not_inst prop1 prop2 inst)
        (inst_not_prop prop1 inst)
    )
 
)
; **********************************************************
; PROP_NOT_INST finds a property p3 of all instances of a property p1
; not shared by the given instance i.
; global variable: poss_props  weird_pred
;
(defun prop_not_inst (prop1 prop2 inst)
   (setq poss_props
         (apply_intersection (get_all_properties (remove inst (get_instances prop1 'true) )))
   )
   (setq poss_props (remove prop1 poss_props))
   (setq poss_props (remove prop2 poss_props))
   (setq weird_pred (car (exclude (get inst 'properties)
                                  poss_props
                         )
                    )
   )
   (cond ( weird_pred
           (list weird_pred (list '$x) 'true)
         )
         (t nil)
    )
)
; *********************************************************
; INST_NOT_PROP finds a property of an instance not shared by any
; instance of a given property.
;
(defun inst_not_prop (prop inst)
   (setq poss_props
         (get inst 'properties)
   )
   (setq weird_pred
        (car (exclude (apply_union (get_all_properties
                                     (remove inst
                                        (get_instances prop 'true)
                                     )
                                   )
                      )
                      poss_props
             )
        )
   )
 
   ( cond ( weird_pred (list weird_pred (list '$x) 'false) )
          ( t nil)
   )
)
; **********************************************************
; GET_ALL_PROPERTIES returns a list of the lists of properties of
; a list of instances.
(defun get_all_properties (instances)
    (mapcar '(lambda (inst)
                (get inst 'properties)
             )
             instances
    )
)
; *****************************************************
; generalization about goal achievement:
; *****************************************************
; GEN_GOAL takes a rule that has started a projection that
; led to a goal, and creates a new rule:
;   conditions & goal --> actions
; this can be thought of both as a generalization about the goal,
; or as a specialization of the rule.
;
(defun gen_goal (rule_list)
   (mapcar '(lambda (rul)
               (make_rule_long (car active_problems)
                               (union (get rul 'conditions)
                                      (make_wants (get (car active_problems) 'goals) t)
                               )
                               (get rul 'actions)
                               (get rul 'slot)
                               (get rul 'status)
                               (get rul 'strength)
                )
            )
            rule_list
    )
)
; ****************************************************************
; MAKE_WANTS takes a list of messages and changes all the truth
; values to want_true or want_false.
; <<Fix to make vbl_lst local variable.  Cf. fix_vbls.>>
(defun make_wants (mess_list gen?)
   (setq vbl_lst univ_vbls)  ; from begin.l
   (prog (m_list mess new_mess new_args result)
         (setq m_list mess_list)
         (setq result nil)
         loop
         (cond ( (null m_list) (return result) ))
         (setq mess (car m_list))
         (cond ( gen? (setq new_args
                            (second (fix_vbls (list 'kluge (second mess) )))
                      )
               )
               ( t (setq new_args (second mess) ) )
         )
         (cond ( (or (equal (third mess) 'true)
                     (equal (third mess) 'want_true)
                 )
                 (setq new_mess (list (car mess)
                                      new_args
                                      'want_true
                                      (fourth mess)
                                 )
                 )
               )
               (t (setq new_mess (list (car mess)
                                       new_args
                                        'want_false
                                       (fourth mess)
                                  )
                  )
               )
       )
       (setq result (cons new_mess result))
       (setq m_list (cdr m_list))
       (go loop)
   )
)		  
; *****************************************************************


; END OF GEN.L    

    

    
(defun load_all ()
   (setq print_to_file nil)
; miscellaneous:  
   (load "/u2/pault/pi/common.l")
   (load "/u2/pault/pi/misc.lbin")
; problem solving:
   (load "/u2/pault/pi/begin.l")
   (load "/u2/pault/pi/prob.l")
   (load "/u2/pault/pi/prob_fire.lbin")
   (load "/u2/pault/pi/prob_spread.l")
   (load "/u2/pault/pi/store.l")
   (load "/u2/pault/pi/analog.l")
   (load "/u2/pault/pi/ana_schem.l")
; induction:
   (load "/u2/pault/pi/concepts.l")
   (load "/u2/pault/pi/explain.l")
   (load "/u2/pault/pi/gen.l")
   (load "/u2/pault/pi/theory.l")
   (load "/u2/pault/pi/trig.l")
; motivation:
  (load "/u2/pault/pi/motiv.l")
; causal reasoning:
;  (load "/u2/pault/pi/cause.l")
(my_print "PI files loaded.")
; data file:
   (load "/u2/pault/pi/data/wts.l")
)
(load_all)

;  FILE:        misc.l
;  PURPOSE:     Miscellaneous utility functions for PI
;  PROGRAMMER:  Paul Thagard
;  CREATED:     5-25-84
;  LAST UPDATE: 6-11-87
;*********************************************************************** 22
;  TRUTH_COMPATIBLE checks that two messages have compatible
;  truth values
(put 'true  'truthkind  't)
(put 'proj_true 'truthkind 't)
(put 'want_true 'truthkind 't)
(put 'false 'truthkind 'f)
(put 'proj_false 'truthkind 'f)
(put 'want_false 'truthkind 'f)
 
(defun truth_compatible (mess1 mess2)
   (put 'true 'truthkind 't)
   (equal (get (third mess1) 'truthkind)
          (get (third mess2) 'truthkind)
   )
)
; ********************************************************************* 
;  MAXIMUM gives the greatest of a list of values
(defun maximum (numlist)
   (apply 'max numlist)
)
;
; ********************************************************************* 
; MAX1 returns no higher than 1:
(defun max1 (num)
   (if (> num 1) 1 num)
)
; *******************************************************
; EXCLUDE (list1 list2) returns a list consisting of list2 with
; all the elements of list1 removed.
(defun  exclude (list1 list2) (set-difference list2 list1))
;**********************************************************
; UNION_LIST takes any number of arguments and returns the
; union of all of them.
(defun union_list (&rest arguments)           ; takes any number of arguments
    (remove-duplicates (apply 'append arguments))
)
; ********************************************************
; UNION_MAP takes the union of all members of a list of lists,
; where the list of lists arises from mapcarring a function.
; e.g. union_map  'cdr  '( (a b) '( 1 2 a)) = (b 2 a)
(defun union_map (fn lst)
   (apply 'union_list (mapcar fn lst))
)
;**********************************************************
; INTERSECTION_LIST takes any number of arguments and returns 
; their intersection.
(defun intersection_list (&rest arguments)
   (prog (args result)
      (setq args arguments
            result nil
      )
      loop
      (cond ( (null args) (return result)))
      (setq result (intersect (car args) result))
      (setq args (cdr args))
      (go loop)
   )
)
;**********************************************************
(defun apply_union (lst)
    (apply 'union_list lst)
)
;
(defun apply_intersection (lst)
    (apply 'intersection_list lst)
)
;**********************************************************
 
;**********************************************************
(defun not_equal (s1 s2)
   (not (equal s1 s2))
)
 
(defun not_member (el lst)
  (cond ( (memberlist el lst) nil )
        ( t t)
  )
)
; ATOMCAR  ; buggy
(defun atomcar (atm)
   (coerce (aref (symbol-name atm) 0) 'atom)
)
; ATOMCDR: modify for commonlisp.
(defun atomcdr (atm)
   (implode (cdr (explode atm)))
)
; 
   
; ***********************************************************
; REMOVE_LIST removes all members of list1 from list2
(defun remove_list (lst1 lst2)
    (prog (ls result)
       (setq ls lst1)
       (setq result lst2)
       loop
       (cond ( (null ls) (return result)))
       (setq result (remove (car ls) result))
       (setq ls (cdr ls))
       (go loop)
    )
)
 
; *********************************************************
;  
; HIGHEST (list property)  returns that member of the list
; which has the highest value on its property list of the
; given property.
 
(defun highest (list property)
   (declare (special property))
   (prog (lst values)
      (setq lst list)
      (setq values (mapcar '(lambda (el)
                               (get el property)
                            )
                            list
                    )
      )
      loop
      (cond ( (null lst) (return nil)))
      (cond ( (equal (get (car lst) property)
                     (apply 'max values)
               )
               (return (car lst))
            )
       )
       (setq lst (cdr lst))
       (go loop)
  )
)
; ****************************************************
; NO_NILS determines if a list has no nil elements.
(defun no_nils (lst)       ;  lst has no nil elements
   (cond ( (null lst) t)
         ( (null (car lst)) nil)
         (t (no_nils (cdr lst)))
   )
)
; *************************************************************
;  slow_print prints everything out on its own line
(defun slow_print (lst)
    (mapcar 'my_print lst)
)
; *************************************************************
; PRINT_PLIST_S prints out the plists of all members of a list
(defun print_plist_s (lst)
    (mapcar 'print_plist lst)
)
 
(defun pls (lst) (mapcar 'print_plist lst))
 
;***************************************************************
 
 
;  DUMP_ALL prints out the property lists of all rules and
;  concepts.
;
(defun dump_all ()
   (my_print '"++++++++++++++++++++++++++++++++++++++++++++++++")
   (my_print '"dumping entire system:")
   (my_print '"all rules:")
   (mapcar 'print_plist
           all_rules
   )
   (my_print '"all concepts:")
   (mapcar 'print_plist
           all_concepts
   )
   (dump_messages)
   (my_print '"active problems:")
   (mapcar 'print_plist
           all_problems
   )
   
)
; ****************************************************************************
; DUMP_MESSAGES prints out all_hypotheses, etc.
(defun dump_messages ()
    (mapcar 'print_plist (union (get 'all_hypothesis 'members)
                                (get 'all_explanandum 'members)
                         )
    )
)
;******************************************************************************
 
;  DUMP_ACTIVE prints out the property lists of all active rules and
;  concepts.
;
(defun dump_active ()
   (my_print '"dumping active system:")
   (my_print '"active rules:")
   (mapcar '(lambda (rul)
              (my_print  rul (plist rul) )
            )
           active_rules
   )
   (my_print '"active concepts:")
   (mapcar '(lambda (conct)
               (my_print  conct (plist conct) )
            )
           active_concepts
 
   )
   (my_print '"active problems:")
   (mapcar '(lambda (prob)
               (my_print prob (plist prob) )
            )
           active_problems
 
   )
   (my_print '"all rules: " all_rules)
   (my_print '"all concepts: " all_concepts)
   (my_print '"*************end dump*******************")
)
; **************************************************************************
; print_plist pretty-prints out a property list.
(defun print_plist (atm)
   (prog (lst)
       (my_print '"   ")
       (my_print '"Property list of "  atm)
       (setq lst (plist atm))
       loop
       (cond ( (null lst) (return t)))
       (my_print (car lst) '":  " (cadr lst))
  
       (setq lst (cddr lst))
       (go loop)
   )
)
(defun pl (atm) (print_plist atm))
;*************************************************************************
; MAKE_NAME makes a name a_b_c_... out of a set of atoms.
(defun make_name (list_of_atoms)
   (apply 'concat list_of_atoms)
)
 
; **********************************************************
; NAME_MESSAGE adds a name to a message, indicating what type
; it is.  The message structure becomes:
; (predicate arguments truth-value confidence name)
; Appropriate names:  goal, explanandum, message, hypothesis.
; global variable:  newname
(defun name_message (mess type)
   (setq newname (newsym type))
   (setq typeclass (concat 'all_ type) )
   (put newname 'data_type type)
   (put newname 'importance 1)     ; default for goals and explananda
   (put typeclass 'members (cons newname (get typeclass 'members)))
   (setf typeclass (cons newname typeclass)) ; won't work
   (put newname 'message
        (cond ( (or (equal type 'goal)
                    (equal type 'event_chain)
                    (equal type 'motive_relevance)
                    (equal type 'search_mess)
                    (equal type 'search_instances)
                )
                (list (car mess) (second mess) 
                      (make_want (third mess))   
	              1	
	              newname
                )
              )
              (t (list (car mess) (second mess)
                       (third mess) (fourth mess)
                       newname
                 )
              )
        )
   ) ; returns message
)
; *********************************************************
(defun make_want (value)
   (cond ( (equal value 'true) 'want_true)
         ( (equal value 'false) 'want_false)
         ( t value)
   )
)
; **********************************************************
; NAME_MESS_LIST does a bunch of messages at once
(defun name_mess_list (mess_list type)
   (cond ( (null mess_list) nil)
         ( t (cons (name_message (car mess_list) type)
                   (name_mess_list (cdr mess_list) type)
             )
         )
   )
) 
;**********************************************************
; useful for mapcarring:
(defun get_solutions (concpt)
;s   (print concpt) 
;s   (print (get concpt 'old_solutions))
;s   (terpri)
   (get concpt 'old_solutions)
)
(defun get_rules (concpt)
   (get concpt 'rules)
)
(defun get_objects (concpt)
   (union_map 'get_argument 
              (get concpt 'instances)
   )
)
(defun get_activation (struc)
    (get struc 'activation)
)
; *******************************************************
; DISPLAY_VALS gives a set of values from plists of a set.
(defun display_vals (lst prop)
        (mapcar '(lambda (atm)
                    (my_print atm)
                    (my_print (get atm prop))
                 )
                lst
        )
)
;**********************************************************
; MESS_ON determines whether a message is on a message list,
; ignoring confidence and name; according to the third argument,
; it returns either the message sought or the one found.
;
(defun mess_on (mess mess_lst sought_or_found)
  (prog (m_list mess_1)
    (setq m_list mess_lst)
    loop
    (cond ( (null m_list) (return nil) ))
    (setq mess_1 (car m_list))
    (cond ( (and (equal (car mess) (car mess_1))
                 (equal (second mess) (second mess_1))
                 (truth_compatible mess mess_1)
            )
            (cond ( (equal sought_or_found 'sought )
                    (return mess)
                  )
                  ( t (return mess_1))
            )
          )
     )
     (setq m_list (cdr m_list))
     (go loop)
   )
)
; *******************************************************
; CLEAR_ALL resets the system, clearing all property lists.
(defun clear_all ()
   (setq to_clear (union_list all_rules all_concepts all_problems
                              all_hypothesis
                              all_explanandum
                              (get 'all_hypothesis 'members)
                              (get 'all_explanandum 'members)
                  )
   )
   
   (mapcar 'clear_props to_clear)
   (init_prob)   ; see prob.l
   (setq all_concepts nil
         all_rules nil
   )
)
(defun nillify (atm)
    (setq atm nil)
)
; CLEAR_PROPS
(defun clear_props (atm)
   (mapcar #'(lambda (prop)
               (put atm prop nil)
            )
            (every_second (plist atm))
    )
)
; ****************************************************
; UN_REFRACT removes a record of previous matches so that
; rules can fire again.
(defun un_refract (rul)
    (put rul 'old_matches nil)
)
; ****************************************************
; EVERY_SECOND gets the first, third, fifth, etc. members
; of a list.
(defun every_second (lst)
    (prog (result)
      (setq ls lst
            result nil
      )
      loop
      (cond ( (null ls) (return result)))
      (setq result (cons (car ls) result))
      (setq ls (cddr ls))
      (go loop)
   )
)
; *******************************************************
; PROJECT_MESS returns an identical message only with
; a projected truth value.
(defun project_mess (mess)
   (subst (project_truth_value (third mess)) (third mess) mess)
)
; *******************************************************
; For name manipulation:
; NEWATOM 
(defun newatom (stem)
   (prog1 (intern (string (gensym stem))))
)
; *******************************************************
 
; *******************************************************
; OBJ_FROM_PROB states all the objects used in a problem.
(defun obj_from_prob (prob)
   (union_map #'second (union (get prob 'start) (get prob 'goals)))
)
; ****************************************************************
; FIND_DUPLICATES names all the redundant members of a list.
(defun find_duplicates (list_of_atoms)
   (do ((lst list_of_atoms (cdr lst))
        (dups nil)
       )
       ; exit:
       ((null lst) dups)
       ; repeat:
       (if (member (car lst) (cdr lst))
           (setq dups (cons (car lst) dups))
       )
    )
)
; ****************************************************************
; CONC_FROM_PROB takes concepts from the
; specification of a problem.
(defun conc_from_prob (prob)
   (remove-duplicates (concepts_from (union (get prob 'start)
                                            (get prob 'goals) 
                                      )
                      )
   )
)
;  ************************************************************************ 
;  CONCEPTS_FROM returns a list of all the concepts used in a list of
;  conditions, actions, or messages
(defun concepts_from (mess_list)
   (mapcar 'car mess_list)
)
;
;  ************************************************************************ 
; CONS_IF_NEW adds an element if it is not already there.
(defun cons_if_new (el lst)
   (if (member el lst) lst
       ; else
       (cons el lst)
   )
)
;  ************************************************************************ 
;  MIN_MAX returns a value between low and high.
(defun min_max (low high num) (min (max low num) high))
;  ************************************************************************ 
;  REMOVE_NIL_DUP removes nil and duplicate elements.
(defun remove_nil[A_dup (lst)
   (remove-duplicates (remove nil lst))
)
;  ************************************************************************ 
; MY_OPEN opens a file for output:
(defun my_open (string)
   (setq where_print_before where_to_print)
   (setq where_to_print     ;  see my_print in common.l
         (open string :direction :output :if-exists :append
                      :if-does-not-exist :create
         )
   )
)
; *********************************************************************
; MY_CLOSE closes an open output file and returns to standard output
(defun my_close (stream)
   (close stream)
   (setq where_to_print where_print_before)
)
; end misc.l

; FILE:        motiv.l
; PURPOSE:     motivated inference
; PROGRAMMER:  Paul Thagard
; CREATED:     8-1-86
; UPDATED:     2-25-87
; See Thagard and Kunda, "Hot Cognition", Proc. Cog. Sci. Soc. 1987.
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
(defun make_self (self_name attributes motives)
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
(defun attributes_of (self)
   (mapcar 'car (get self 'attributes))
)
; MOTIVES_OF
(defun motives_of (self)
   (mapcar 'car (get self 'motives))
)
; ATTRIB_ACTIVN_OF
(defun attrib_activn_of (self attrib)
   (second (assoc attrib (get self 'attributes)))
)
; ATTRIB_MESS_OF
(defun attrib_mess_of (self attrib)
   (third (assoc attrib (get self 'attributes)))
)
; ATTRIB_MESSAGES_OF 
(defun attrib_messages_of (self)
   (third_s (get self 'attributes))
)
; 
; ATTRIB_IMPORT_OF
(defun attrib_import_of (self attrib)
   (fourth (assoc attrib (get self 'attributes)))
)
; MOTIV_MESS_OF
(defun motiv_mess_of (self motiv)
    (third (assoc motiv (get self 'motives)))
)
; MOTIV_MESSAGES_OF
(defun motiv_messages_of (self)
    (third_s (get self 'motives))
)
; MOTIV_ACTIVN_OF
(defun motiv_activn_of (self motiv)
   (second (assoc motiv (get self 'motives)))
)
; MOTIV_PRIOR_OF
(defun motiv_prior_of (self motiv)
    (fourth (assoc motiv (get self 'motives)))
)
; THIRD_S returns a list of all the third elements of items in a list.
(defun third_s (lst)
   (mapcar 'third lst)
)
; NAME_FROM_GOAL
(defun name_from_goal (goal_mess)
   (fifth goal_mess)
)
; *********************************************************************
; PRINT_SELF prints out a self and
; associated attributes and motives.
(defun print_self (self)
   (my_print '"Self: " self)
   (my_print '"   Attributes: ")
   (mapcar 'print_attrib (get self 'attributes))
   (my_print '"   Motives: ")
   (mapcar 'print_motiv (get self 'motives))
)
; **********************************************************
; PRINT_ATTRIB prints out attribute.
(defun print_attrib (attr_lst)
   (my_print '"      Attribute: " (car attr_lst))
   (my_print '"         Activation: " (second attr_lst))
   (my_print '"         Message: " (third attr_lst))
   (my_print '"         Importance:  " (fourth attr_lst))
   
)
; **********************************************************
; PRINT_MOTIV prints out motive.
(defun print_motiv (mot_lst)
   (my_print '"      Motive: " (car mot_lst))
   (my_print '"         Activation: " (second mot_lst))
   (my_print '"         Message: " (third mot_lst))
   (my_print '"         Priority: " (fourth mot_lst))
)
; ****************************************************************
;         Determining the relevance of a conclusion to the self.
; ***************************************************************
; MOTIVE_RELEVANCE determines the relevance of a possible conclusion to
; a self.  Returns 0 if conclusion is 
; irrelevant, between -1 and 0 if it goes against
; accomplishing a goal, and between 0 and 1 if it contributes to a goal.
(defun motive_relevance (self message)
   (prog (motivs)
      (my_print '"What is relevance of " message '" to " self '"?")
      (setq motivs (rel_motives self message))
      (setq result 0)
      loop
      (cond ( (null motivs) 
              (my_print '"Overall relevance of " message '" to "
                        self '" is:  " result
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
; and there are rules A -> B, B ->C, and C -> M, where M is a motive,
; then A is relevant to M. Relevance can be positive or negative,
; depending on truth values: it's good if you want something to be
; true and it is.
(defun rel_motives (self mess)
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
                (my_print '"Motives of self "  self '" relevant to "
                          mess '" are: "  goal_sat_messages
                )
                (put (car mess) 'relevant_motives  ; store for rationalise
                   (cons (list self (concepts_from goal_sat_messages))
                           (get (car mess) 'relevant_motives)
                     )
                )  
                goal_sat_messages
              )
              ( t (my_print mess '" is irrelevant to " self)
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
(defun motives_accomplished (mess goal_list mess_list)
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
(defun counter_satisfied (goal mess_list)
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
(defun motiv_value (self motive_mess message)
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
(defun motive_direction (mot_mess mess)
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
(defun motiv_gen (self class property)
   ; announce
   (my_print '"**********************************************")
   (my_print '"Motivated generalization by " self '":  "
              class '" -> " property '" ?" 
   )
   (let ( (relevance (motive_relevance self ;
                                       (list property (list self) 'true)
                     ) ; relevance of self being B.
          )
          (basic_threshold gen_threshold)   ; for gen_threshold see gen.l
          (gen_done? nil)
        )
         
        ; if being B is good, try to show that S is A and that A->B:
        
        (cond ( (> relevance 0)
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
        (cond ( (< relevance 0)                       
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
        (my_print '"Generalization threshold is now: " gen_threshold)
        (my_print '"Number of instances needed for generalization is: "
                  (times gen_threshold max_instances)
        )
        ; now generalize as before.
        (setq gen_done? (generalize (list class property nil)))  ; see gen.l
        ; if generalizing occurred despite negative relevance, adjust self.
       
        (cond ( (and gen_done? (< relevance 0))
                (rationalise self property)
              )
        )
        ; set back gen_threshold
        (setq gen_threshold basic_threshold)
   )
)
; **************************************************
; MAKE_SELF_MESSAGE sets up a message involving the self:
(defun make_self_message (self predicate truth_val)
   (list predicate (list self) truth_val)
)
; ***************************************************
; IS_SELF? determines whether a concept applies to a self.
(defun is_self? (self conc)
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
(defun motive_relevance_of_rule (self class property)
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
(defun attribute_relevant? (self mess)
   (cond ( (mess_on mess (attrib_messages_of self) 'sought)
           (my_print '"Attribute " mess '" does apply to " self)
           t
         )
         (t (my_print '"Attribute " mess '" does not apply to " self)
            nil
         )
   )
)
; ***************************************************
; SELF_INSTANTIATE plugs a self into the argument in a message.
(defun self_instantiate (self mess)
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
(defun rationalise (self attrib)
   (prog (motives)
      (setq motives (second (assoc self (get attrib 'relevant_motives))))
      (my_print '"Rationalization  by " self
                '" through  reduction of priority of motives "
                motives
      )
      loop
      (if (null motives) (return '"Rationalizing done."))
      (reduce_priority self (car motives))
      (setq motives (cdr motives))
      (go loop)
   )
)
; ***************************************************
; REDUCE_PRIORITY lowers the priority of a self's motive.
(defun reduce_priority (self motive)
   (let ( (old_mot (assoc motive (get self 'motives)))
        )
        (my_print '"OLD " old_mot)
        (put self 'motives
             (cons (list motive (second old_mot) (third old_mot)
                         (/ (fourth old_mot) motiv_redn)
                   )
                   (remove old_mot (get self 'motives) :test 'equal)
             )
        )
        (my_print '"Priority of motive " motive '" of " self
                  '" reduced to " (motiv_prior_of self motive)
        )
   )
)
; ***************************************************
; REMOVE_ATTRIB/MOTIV deletes an attribute
; or motive from a self.
(defun remove_attrib/motiv (self attr kind)
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
(defun search_mess (self mess urgency)
   (let ( (prob (newsym 'search_mess))
           (old_time timesteps)
           (result nil)
        )
        (my_print '"Attempting to show " mess)
        (init_prob)
        (setq timesteps (urgency_to_time urgency))
        (make_problem prob
                      (attrib_messages_of self)
                      (list mess)
                      'search_mess
         )
         (setq result  (solve_problem prob))
         (setq timesteps old_time)
         (if result (my_print '"Search showed: " mess)
                    ; else
                    (my_print '"Search failed: " mess)
         )
         result
   )
)
; ****************************************************************
; URGENCY_TO_TIME translates the urgency of an inference into 
; the number of timesteps a problem should run.
(defun urgency_to_time (urg)
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

(defun search_instances (self mess1 mess2 urgency)
   (let ( (prob (newsym 'search_instances))
           (old_time timesteps)
           (result nil)
        )
        (my_print '"Searching for instances of " mess1 '" and " mess2)
        (my_print '"Known instances of " (car mess1) '" before search: " 
                  (get (car mess1) 'instances)
        )
        (my_print '"Known instances of " (car mess2) '" before search: " 
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
         (my_print '"Known instances of " (car mess1)
                   '" after search: " (get (car mess1) 'instances)
         )
         (my_print '"Known instances of " (car mess2)
                   '" after search: " (get (car mess2) 'instances)
         )
   )
)
; ****************************************************************       
; MAKE_SEARCH_MESS  constructs a message that will never actually
; be matched fully, but which will help to direct subgoaling.
                       
(defun make_search_mess (conc)
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
(defun decide (self list_of_acts)
   (prog (acts best_act)
      (setq acts list_of_acts)
      (cond ( (null acts) 
              (setq best_act (highest list_of_acts value))
              (my_print '"Decision:  "  best_act '" is the best act.")
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
(defun set_decision_value (self act)
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
   
(defun init_prob ()
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
 
(defun de_activate (struc)
   (put struc 'activation 0)
   (put struc 'forward_activated_by nil)
   (put struc 'goal_activated_by nil)
)
;*************************************************************************** 1
;  SOLVE_PROBLEM (prob_name) attempts to solve the given problem.
 
(defun solve_problem (prob_name)
   (declare (special best_rules))
   (cond (  trace_prob
            (my_print '"------------------------------------------")
            (my_print  '"SOLVING PROBLEM:  " prob_name )
            (my_print  '"STARTING FROM:  "   (get prob_name 'start))
            (my_print  '"GOALS:  "  (get prob_name 'goals) )
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
  
;        (my_print '"DEBUG active_messages: " active_messages)
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
                 (my_print (car active_problems) '" solved.")
                 ;(cond ( print_to_file (princ '"Problem solved.")))
                 (return t)
               )
         )
 


         (cond ( (or (equal clock timesteps)
                     (and ; (null analogy_flag)
                          (> clock 2) 
                          (null best_rules)      ; nothing fired at last step
                          (null just_activated)  ; no new concepts activated
                          (null activated_last_time)
                          (null goal_activated)
                     )
                 )                          ; see prob_fire.l.
                 (my_print '"Solution failed for " (car active_problems))
                 (my_print '"---------------------------------------------")
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
(defun projecting_rules (prob_nam)
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
 
(defun start_projection (effector)
   (setq proj_name (newsym 'proj_))
   (put proj_name 'first_effector effector)
   (setq active_projections (cons proj_name active_projections))
    
   (cond ( trace_prob
           (my_print  '"Starting projection " proj_name
                      '" from " effector
           )
           ;(my_print '"NOW_EFFECTS " (get (car active_problems) 'effects)) ;!!!
         )
    )
)
; ************************************************************* 3
; STOP_PROJECTION ends a projection.
; global variable:  effector
(defun stop_projection (projn)
   (setq effector (get projn 'first_effector))
   (cond (trace_prob (my_print  '"Projection " effector '" from "
                                projn '" stopped."
 
                     )
          )
   )
   ; erase projected effects:
   (put (car active_problems) 'effects
        (remove effector (get (car active_problems) 'effects) )
   )
   ;(my_print '"Now_effects: " (get (car active_problems) 'effects))  ;!!!!
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
(defun remove_mess (conc mess_list)
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
 
(defun pi_status (prob cloc)
   (my_print '"----------------------------------------------")
   (my_print  '"PROBLEM:  " prob   '"     TIMESTEP:  " cloc )
   (cond ( print_to_file (print "FIRED " )
                         (print best_rules)
                         (terpri)
                         (print cloc)
                         (terpri)
         )
   )
   (my_print  '"Active messages:  " (remove_confidences active_messages ))
   (my_print  '"Active concepts:  " active_concepts )
   (my_print  '"Concept activations:  "
            (mapcar 'get_activation active_concepts)
  )
   (my_print  '"Active rules:  "    active_rules )
   (my_print  '"Active problem solutions:  " active_solutions)
   (my_print  '"Solution activations:  "
              (mapcar 'get_activation active_solutions)
   )
   (my_print  '"Subgoals:  "   (get (car active_problems) 'sub_goals) )
   (my_print  '"Active projections:  "  active_projections )
)
; ************************************************************************ 4b
; REMOVE_CONFIDENCES returns a list of messages with no confidence value.
(defun remove_confidences (mess_lst)
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
(defun observe ()
   (cond ( environment_made
           (my_print '"observing environment")
         )
    )
)
;  ************************************************************************ 6
;  CONCEPTS_FROM returns a list of all the concepts used in a list of
;  conditions, actions, or messages
(defun concepts_from (mess_list)
   (mapcar 'car mess_list)
)
;
;*************************************************************************** 7
;  CHECK_FOR_SUCCESS checks whether the goals are now all on the
;  message list, i.e. have been accomplished.
;  global variable:  contradiction
(defun check_for_success (problem_name)
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
                              (my_print '"Problem not yet solved")
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
(defun accomplished (goal_list mess_list)
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
 
(defun is_satisfied (goal mess_list)
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
(defun arg_equal (args1 args2)
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
 
(defun truth_satisfies (mess1 mess2)
   (and (not_equal (third mess1) 'want_true)
        (not_equal (third mess1) 'want_false)
        (truth_compatible mess1 mess2)
   )
)   
;************************************************************************** 10
 
;  CONTRADICT returns t if any member of the first list is incompatible with
;  any member of the second.
 
(defun contradict (mess_list_1 mess_list_2)
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
                          ; ignore "want" truth values:
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
 
(defun reward (rule_list)
   (cond ( trace_prob
           (my_print  '"rewarding:  " rule_list )
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
 
(defun punish (rule_list)
   (cond ( trace_prob
           (my_print  '"punishing:  " rule_list )
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


;  FILE:        prob_fire.l
;  PURPOSE:     Problem solving in PI:  rule firing
;  PROGRAMMER:  Paul Thagard
;  CREATED:     10-11-85   (from prob)
;  LAST UPDATE:  12-2-86
;********************************************************************* 13
;  FIRE_RULES () fires the best of the active_rules, putting their
;  instantiated actions on the message list.
 
(defun fire_rules ()
    (declare (special best_rules) )
;   evaluate all the active rules
    (mapcar 'evaluate active_rules)
;   select the best rules
    (setq best_rules (reverse (select_rules max_rules)))
;   execute the actions of the best rules
    (cond ( trace_prob
            (my_print '"FIRING RULES:  " best_rules)
          )
    )
    (cond ( (null active_projections)
            (put (car active_problems) 'rules_used
                 (union (get (car active_problems) 'rules_used)
                        best_rules
                  )
             )
          )
          (t (put (car active_problems) (car active_projections)
                    (union best_rules
                           (get (car active_problems)
                                (car active_projections)
                           )
                     )
                )
             )
    )
    (execute_actions best_rules)
)
;*********************************************************************** 14
;
;  SELECT_RULES selects the best num of the currently active rules.
 
(defun select_rules (num)
   (prog (rules count values result bad_rules rul1)
         (cond ( (null active_rules) (return nil) ))
         (setq rules active_rules
               count 0
               result nil
               bad_rules nil
         )
         loop1
         (setq values
               (mapcar '(lambda (rul)
                           (get rul 'current_value)
                        )
                        rules
               )
         )
         (cond ( (or (equal count num)
                     (null rules)
                 )
                 (return result)
               )
         )
         loop2
         (cond ( (null rules) (return result) ) )
;        check first rule to see if it has highest value and meets other criteria
         (setq rul1 (car rules))
         (cond ( (equal (get rul1 'current_value)
                        (apply 'max values)
                 )
                 (cond ( (and (no_effector_conflict rul1
                                                    (get (car active_problems) 'effects)
                              )
                              (not_equal 0 (get rul1 'current_value) )
                              (not_redundant rul1)
                              ; not formed abductively:
                              (not_equal 'abduced (get rul1 'how_formed))
                         )
                         (setq result (cons rul1 result))
                         (setq count (add1 count))
                         (put rul1 'old_matches
                              (cons (get rul1 'current_match)
                                    (get rul1 'old_matches)
                              )
                         )
                         (update_effects rul1)    ; note effec
                       )
                       (t (setq bad_rules (cons rul1 bad_rules)))
                 )
                 (setq rules (exclude (union result bad_rules)
                                      active_rules
                             )
                 )
                 (go loop1)
               )
         )
         (setq rules (cdr rules))
         (go loop2)
    )
)
; ************************************************************** 14a
; UPDATE_EFFECTS keeps track of what effects are authorized, in order
; to prevent conflicts.
(defun update_effects (rul)
    (declare (special rul))
    (mapcar '(lambda  (actn)
                (cond ( (equal (get_effect_status actn) 'effect)
                        (put (car active_problems) 'effects
                             (cons (car actn)
                                   (get (car active_problems) 'effects)
                             )
                        )
                        ; for the sake of analogy:
                        (put (car active_problems) 'effects_objs
                             (cons (list (car actn) 
                                         (second (car (get rul
                                                           'action_instances
                                                      )
                                                  )
                                         )
                                   )
                                   (get (car active_problems) 'effects_objs)
                             )
                        )
                      )
                )
             )
             (get rul 'actions)
    )
)
;******************************************************************* 15
;  NO_EFFECTOR_CONFLICT makes sure that a rule to be fired does
;  not have an effector incompatible with one already selected.
;  Bug:  this is simplistic, in that it does not distinguish between
;  two effectors that cannot be done at the same time, and two that can
;  not be done in the same sequence.
 
(defun no_effector_conflict (rul effect_list)
   (prog (actns actn)
         (cond ( (null effect_list) (return t) ))
         (setq actns (get rul 'action_instances))
         loop
         (cond ( (null actns) (return t) ) )
         (setq actn (car actns))
         (cond ( (equal 'effect (fifth actn) )
                 (cond ( (eff_conflict (car actn) effect_list) (return nil)))
               )
         )
         (setq actns (cdr actns))
         (go loop)
    )
)
;*********************************************************************** 15a
 ; EFF_CONFLICT checks whether an effect conflicts with one already
 ; executed.
 ;
(defun eff_conflict (effect effect_list)
    (prog (e_list)
          (setq e_list effect_list)
          loop
          (cond ( (null e_list) (return nil) ))
          (cond ( (check_conflict effect (car e_list) )
                  (return t)
                )
          )
          (setq e_list (cdr e_list))
          (go loop)
     )
)
; **************************************************************15
; CHECK_CONFLICT sees whether two effects are incompatible.
(defun check_conflict (eff1 eff2)
    (member (list eff1 eff2) effector_conflicts)   ; set by data
)
; *****************************************************************15
; NOT_REDUNDANT checks that a rule has not already been fired with a given
; set of matching instances.
 
(defun not_redundant (rul)
   (not (memberlist (get rul 'current_match)
                    (get rul 'old_matches)
        )
   )
)
;********************************************************************** 16
;  EVALUATE (rule_list) performs the following functions for each rule:
;    1. checks if all the rule's conditions are matched by active
;       messages
;    2. instantiates the actions of the rule, if the match permitted
;    3. calculates the overall value of the rule as:
;         minimum confidence of conditions matched * strength * activation
;       note that the activation of the rule was calculated when
;       active_rules was updated by change_activation
;       N.B.  change this to recurse on active messages not used, to
;       allow a rule to be fired twice, on different instances.!
 
(defun evaluate (rul)
;   intialize variables:
    (mapcar 'delete_binding vbl_list)
    
;   defaults for confidence of matches and matching objects:
    (put rul 'condn_confidences '( 1 )) 
    (put rul 'current_match nil)           
    (setq more_than_flag nil)
 
    (prog (condns min_confidence messages  first_mess)
          (setq condns (get rul 'conditions))
          ; for each condition:
          loop1
          ; if done, calculate current value
          (cond ( (null condns)
                  (setq min_confidence (apply 'min
                                              (get rul 'condn_confidences)
                                       )
                  )
                  (put rul 'current_value
                            (times min_confidence
                                   (get rul 'strength)
                                   (get rul 'activation)
                            )
                  )
                  (put rul 'action_instances 
                      (build_actions rul 
                                     (times min_confidence 
                                            (get rul 'strength)
                                     )
                      )
                  )
                  (return (get rul 'current_value))
                )
          )
          (setq messages active_messages)
          ;  match each message:
          loop2
          (cond ( (null messages)
                  (put rul 'current_value 0) ; match failed
                  (return 0)
                )
          )
          (setq first_mess (car messages))
          (cond ( (match (car condns)  first_mess rul)  ; if matches:
                  ;check for projection:
                  (cond ( (or (equal (third first_mess)
                                     'proj_true
                              )
                              (equal (third first_mess)
                                      'proj_false
                              )
                          )
                          (put rul 'proj_status t)
                          (put rul 'matched_projections
                               (union (projn_from_mess first_mess)
                                      (get rul 'matched_projections)
                               )
                          )
                        )
                  )
                  (setq condns (cdr condns))
                  (go loop1)
                )
                (t (setq messages (cdr messages))
                   (go loop2)
                )
          )
    )                                   ; end prog
;   if rule would accomplish a goal, boost its value:
    (cond ( (and (get rul 'satisfies_goal?)
                 (not (equal (get rul 'current_value) 0))
            )
            (put rul 'current_value
                 (max1 (add (get rul 'current_value) .1))
            )
          )
     )
)
;  end of evaluate
; ****************************************************************** 17
;  DELETE_BINDING just removes a variable's binding:  see BINDB below
(defun delete_binding (vbl)
   (put vbl 'binding nil)
)
;******************************************************************* 18
;  MATCH checks for a  match between a condition and a message,
;  binding up the variables in the condition.
 
(defun match (condn message rul )
   (setq match_answer nil)
   (cond ( (and (equal (car condn) 'more_than)             ; kluge
                (null more_than_flag)            ;  double kluge
                (car (get_binding (second condn)))
                (second (get_binding (second condn)))
            )
            (setq more_than_flag t)
            (setq match_answer
                  (greaterp (car (get_binding (second condn)))
                           (second (get_binding (second condn)))
                  )
             )
          )
          (t ( setq match_answer
                    (and (equal (car condn) (car message) )     ; predicates
                         (bind (second condn)                   ; arguments
                               (second message)
                         )
                         (truth_compatible  condn message)     ; truth value
                         (no_want condn message)               ; kluge
                    )
             )
          )
    )
    (cond ( match_answer
            (put rul 'current_match
                      (cons (second message)
                            (get rul 'current_match)
                      )
            )
            (put rul 'condn_confidences
                 (cons (get_confidence message) (get rul 'condn_confidences) )
            )
          )
     )
     match_answer      ; return t or nil
)
;*********************************************************************** 19
; BIND  binds the variables in the first list
;   to the values in the second.  e.g. (bind '(x y) '(fred john))
;   gives x the binding 'fred.
; <<bug:  will screw up if there are two conditions with same predicate,
;   e.g. (planet ($x)) and (planet ($y) ).  Can't deal with identities.>>
(defun bind (arg_list1 arg_list2 )
   (prog (list1 list2 arg1 arg2)
         (setq list1 arg_list1
               list2 arg_list2
         )
         (cond ( (not (equal (length list1) (length list2)))
                 (my_print '"Error:  wrong number of arguments " 
                            list1 list2
                 )
               )
         )
         loop
         (cond ( (null list1) (return t)))
         (setq arg1 (car list1)
               arg2 (car list2)
         )
         (cond ( (numberp arg1) t)                   ; ignore numbers
               ( (is_variable arg1)
                 (cond ( (null (get arg1 'binding))
                         (put arg1 'binding arg2)     ;bind variable
                       )
                       (t (cond ( (not (equal (get  arg1 'binding)
                                              arg2
                                       )
                                  )
                                  (return nil)
                                )
                           )
                       )
                  )
               )
               (t (cond ( (not (equal arg1 arg2))
                          (return nil)
                        )
                  )
               )
          )
          (setq list1 (cdr  list1)
                list2 (cdr  list2)
          )
          (go loop)
   )
)
;***************************************************************** 20
; GET_BINDING replaces variables in an action with the values to which
; they were bound in the conditions.
;
(defun get_binding (arg_list)
   (mapcar '(lambda (arg)
               (cond ( (atom_begins arg #\%) arg) 
                     ( (numberp arg) arg)
                     ( (is_variable arg)
                       (get  arg 'binding)
                     )
                     (t arg)
               )
             )
             arg_list
    )
)
 
 
;********************************************************************** 21
;  IS_VARIABLE returns t if an argument is a variable, otherwise nil.
 
(defun is_variable (arg)
   ( or (atom_begins arg #\$)        ; universal variable
        (atom_begins arg #\%)        ; existential variable
        
   )
)
;*********************************************************************** 22
; TRUTH_COMPATIBLE:  moved to misc.l
;*********************************************************************** 22a
; NO_WANT stops the matching of a want-true message by
; a true condition.  
(defun no_want (mess1 mess2)
   (not (and (atom_begins (third mess2) #\w)
             (or (equal (third mess1) 'true)
                 (equal (third mess2) 'false)
             )
        )
   )
)
;************************************************************************ 23
;  BUILD_ACTIONS uses information gathered while matching a
;  condition to build the action of rule.
;  Note that data files define rule actions just as: 
;       (predicate arguments truth-value deduce/effect).
;  Build actions produces actions for execution of the form:
;       (predicate arguments truth-value confidence deduce/effect).
(defun build_actions (rul confidence)
    (prog (actns act result)
          (setq actns (get rul 'actions)
                result nil
          )
          loop
          (cond ( (null actns) (return result) ))
          (setq act (car actns))
          (setq result
                (cons (list (car act)              ; predicate
                            (get_binding (second act)) ; arguments
                            ; truth value:
                            (cond ( (get rul 'proj_status) ; 
 				    ; for projected value, note origin
                                    (list (project_truth_value  (third act))
                                          (get rul 'matched_projections)
                                    )
                                  )
                                  (t (third act))
                             )
                             confidence
                             (fourth act)
                       )
                       result
                 )
          )
           (setq actns (cdr actns))
           (go loop)
    )
)
;**************************************************************** 23a
; CONCLUSION_CONFIDENCE of a rule is how confident to be about the conclusions
; based on the confidence of the messages which matched the conditions and
; the strength of the rule.  <<not used>>
 
(defun conclusion_confidence (rul)
   (times (get rul 'strength)
          (apply 'min (get rul 'condn_confidences))
   )
)
;********************************************************************* 24
;  PROJECT_TRUTH_VALUE returns a projected truth value.
 
(defun project_truth_value (val)
   (cond ( (atom_begins val #\p)
           val
         )
         ( (equal val 'true)
           'proj_true
         )
         (t 'proj_false)
    )
)
 
; end of prob_fire.l; FILE:        prob_spread.l
; PURPOSE:     problem solving in PI:  spreading activation
; PROGRAMMER:  Paul Thagard
; CREATED:     10-11-85 (from prob)
; UPDATED:     1-13-87
;******************************************************************* 25
; CHANGE_ACTIVATION () updates the activation of concepts, rules,
; messages, and problem solutions.
; The global variable activated_last_time keeps track of what concepts were
; activated the last timestep.  Contrast just_activated which keeps track
; of which concepts were just activated by execute_actions on the current
; timestep.
 
(defun change_activation ()
;d  (my_print '"DEBUG change_activation just_activated " just_activated
;d       '" activated last time " activated_last_time
;d  )


; use rules to activate concepts:  already done by execute_actions (below)
; see also subgoaling activations:  build_sub_goals

; activate superordinates and subordinates of concepts activated in last
; round
   (mapcar 'activ_ordinates activated_last_time)
; prune weak concepts:
   (mapcar '(lambda (concpt)
               (cond ( (lessp (get concpt 'activation)
                             min_activ
                        )
                        (setq active_concepts
                           (remove concpt active_concepts)
                        )
                     )
               )
             )
            active_concepts
    )
; use concepts to activate rules.
;     This would be more sophisticated if activation of a rule were
;     a function of all the concepts to which it is attached, taking into
;     account degree of attachment.
   (setq active_rules (union_map 'get_rules active_concepts))
   (set_activations active_rules 1)
; activate old problem solutions, except for failed ones:
   (setq active_solutions 
         (remove_list (get (car active_problems) 'bad_ana_problems)
                      (union_map 'get_solutions active_concepts)
         )
   )
   (set_activations active_solutions .5)
  
; activate attached objects.  Not yet implemented.
; (setq active_objects (union_map 'get_objects active_concepts))
; (set_activations active_objects 1)
;  eliminate rule to be explained from active rules:
   (setq active_rules (remove (get (car active_problems) 'rule_explanandum)
                              active_rules
                       )
   )
; use concepts to activate messages:
   (setq active_messages   (retrieve_messages ) )
; set up activation for next time:
(setq activated_last_time just_activated)
(setq just_activated nil)
;  kluges:
    (setq active_concepts (remove_duplicates active_concepts) )
    (setq active_messages (remove_duplicates active_messages))
    (setq active_rules (remove_duplicates active_rules))
)
; add:  decrease activation of all concepts before pruning!
; ******************************************************************** 26
; ACTIV_ORDINATES activates the super- and sub-ordinates of a concept.
(defun activ_ordinates (concept)
   (prog (ordinates first_ord result)
      (setq ordinates (append (get concept 'superordinates)
                              (get concept 'subordinates)
                      )
      )
      (setq result nil)
      
     
      loop
      (cond ( (null ordinates)
              (cond ( result
                      (my_print '"Activating "
                                (cond ((only_one result) '"concept ") 
                                      (t '"concepts ")
                                )
                                result
                                '" by hierarchical spread from "
                                concept
                      )
                    )
              )
              (setq just_activated (union result just_activated))  
              (return active_concepts) 
            )
      )
      (setq first_ord (car ordinates))
      ; if first_ord was not active, activate it:
      (cond ( (not_member first_ord active_concepts)
              (setq result (cons first_ord result))
              (setq active_concepts (cons first_ord active_concepts))
              (put first_ord 'forward_activated_by 
                   (cons concept (get first_ord 'forward_activated_by))
              )
              (put first_ord 'activation (get concept 'activation))
            )
            ; if first_ord is active, but has not been activated by concept:
            (t (cond ( (not_member concept (get first_ord 'forward_activated_by))
                       (put first_ord 'activation 
                            (max1 (add (times (get concept 'activation)
                                              incr_activ
                                        )
                                        (get first_ord 'activation)
                                   )
                             )
                        )
                     )
                )
            )
      )
      (setq ordinates (cdr ordinates))
      (go loop)
   )
)
      				             
; ******************************************************************** 26a
; ONLY_ONE 
(defun only_one (lst)
   (equal (length lst) 1)
)
;********************************************************************* 27
 
; SET_ACTIVATIONS increases the activation of 
; structures, each of which can be a
; rule, a problem solution, or an object.  Activation is the sum of 
; activations of concepts to which the structure is attached.
; The second argument is the proportion of activation of the structure to
; be passed along, ranging from 0 to 1.  The higher this number, the
; faster activation will sum.
 
(defun set_activations (strucs fraction)
   (cond ( (null strucs) nil)
         (t (set_activation (car strucs) fraction)
            (set_activations (cdr strucs) fraction)
         )
   )
)
(defun set_activation (struc fraction)
   (put struc 'activation
              (max1
                      (times fraction
                             (apply '+
                                    (mapcar 'get_activation
                                             (get struc 'attached_concepts)
                                    ) 
                             )
                      )
              )
   )
)
;****************************************************************** 28
; RETRIEVE_MESSAGES () constructs messages from instances stored with
; concepts.  it constructs two registers:  known_messages which are
; messages inferred from other known messages, and projected_messages
; which are messages derived from projections.
; in addition, if the flag goals_to_messages is set, it adds
; a list of messages derived from goals, with want truth values.
;
(defun retrieve_messages ()
   (prog (lst concpt result)
         (declare (special concpt))
         (setq lst active_concepts
               known_messages nil
               projected_messages nil
         )
         loop
         (setq concpt (car lst))
         (cond ( (null lst) (setq result (union known_messages
                                                projected_messages
                                          )
                            )
                            (cond ( goals_to_messages
                                    (setq result (union result
                                                        (make_wants (get (car active_problems) 'goals) nil)
                                                  )
                                     )
                                   )
                            )
                            (return result)
               )
         )
         (setq known_messages
               (union known_messages
                      (get concpt 'instances)
               )
         )
         (setq projected_messages
               (union projected_messages
                      (apply 'union_list
                             (mapcar '(lambda (proj)
                                         (get concpt proj)
                                      )
                                      active_projections
                             )
                      )
               )
         )
          (setq lst (cdr lst))
          (go loop)
   )
)
;******************************************************************* 29
; EXECUTE_ACTIONS carries out the actions of fired rules, putting
; the concepts from those actions on the active concepts list.
; <<break this code up>>
 
(defun execute_actions (rule_list)
   (prog (lst new_concepts new_actions)
         (setq lst          rule_list
               new_concepts nil
         )
         loop
         (cond ((null lst) (return nil)))
         (setq rul (car lst))
         ; (cond ( (defective_action rul) (return nil)))
;       get new concepts from actions of rule
         (setq new_actions
               (get rul 'action_instances)
         )
         (setq new_concepts
               (concepts_from new_actions)
         )
         
;       note how concepts were activated, i.e. from what concepts
         (record_activation rul new_actions)
         (cond ( (not_member (car new_concepts) active_concepts)
                 (my_print '"Activating concept " new_concepts 
                           '" by firing rule "   rul		    
                 )
               )
          )       
;       make new concepts active
         (setq active_concepts
               (union active_concepts
                      new_concepts
               )
         )
;        set up activation history for change_activation:
         (setq just_activated (union just_activated new_concepts))
;       increase activation of new concepts and concepts from condititions of fired rules
         (mapcar '(lambda (concpt)
                     (put concpt 'activation
                          (max1
                                 (add (times (get rul 'current_value)
                                             incr_activ
                                       )
                                       (get concpt 'activation)
                                  )
                           )
                      )
                  )
                  (union new_concepts
                         (concepts_from (apply 'union_list
                                               (mapcar '(lambda (rul)
                                                           (get rul 'conditions)
                                                        )
                                                        best_rules   ; rules fired:  see fire_rules
                                                )
                                         )
                          )
                  )
         )
;       store inferred messages with concepts
         (mapcar 'store_actions new_actions)
;       put rule on list of rules used
         (cond ( (get rul 'proj_status)
                 (put (car active_problems)
                      (car active_projections)
                      (cons rul (get (car active_problems)
                                     (car active_projections)
                                 )
                       )
                  )
               )
               (t (put (car active_problems)
                       'rules_used
                       (cons rul
                             (get (car active_problems)
                                   'rules_used
                              )
                       )
                   )
               )
         )
         (setq lst (cdr lst))
         (go loop)
    )
)
; ************************************************************* 29A
; DEFECTIVE_ACTION prevents the execution of a defective action,
; one with a nil or existential argument.
(defun defective_action (rul)
   (prog (args)
      (setq args (union_map 'get_argument
                            (get rul 'actions)
                 )    
      )
      loop
      (cond ( (null args) (return nil)))
      (cond ( (or (null (car args))
                  (is_existential (car args))
              )
              (return t)
            )
      )
      (setq args (cdr args))
      (go loop)
   )
)
    
; IS_EXISTENTIAL 
(defun is_existential (vbl)
   (atom_begins vbl #\l)
)
; *************************************************************  30
; RECORD_ACTIVATION stores with each concept the set of concepts
; that were directly responsible for its activation, i.e.
; the concepts in the conditions of the rule whose firing led
; to the activation of the concept.
(defun record_activation (rul actions)
   (prog (concpt  actns activating_concepts)
      (setq actns actions)
      (setq activating_concepts 
            (concepts_from (get rul 'conditions))
      )
      loop
      (cond ( (null actns) (return t)))
      (setq concpt (caar actns))
      (put concpt 'forward_activated_by
                  (union (get concpt 'forward_activated_by)
                         activating_concepts
                  )
      )
      (setq actns (cdr actns))
      (go loop)
   )
)
       
;*************************************************************  33
 
; SET_SUB_GOALS revises the list of current subgoals.   [33]
; first it updates the list of subgoals by removing subgoals
; which have been accomplished, i.e. are active messages.
; then it builds new sub-goals by checking the list of active
; rules against the current goals and sub-goals.  if a rule has
; the form c -> a and instantiating a would accomplish a goal or
; sub-goal, then c is added as a subgoal.
;
(defun set_sub_goals ()
   (setq goal_activated nil)
   (mapcar 'update_sub_goals (get (car active_problems) 'sub_goals))
   (put (car active_problems) 'sub_goals
        (remove_duplicates (get (car active_problems) 'sub_goals))
   )                               ; kluge
   (mapcar 'sub_goal_find active_rules)
)
;**************************************************** 34
;
; UPDATE_SUB_GOALS deletes a sub-goal if the message list indicates it has
; already been accomplished.
;
(defun update_sub_goals (diff_g)
    (cond ( (member sub_g active_messages)
            (put (car active_problems) 'sub_goals
                  (remove sub_g (get (car active_problems) 'sub_goals))
            )
          )
    )
)
;***********************************************************  35
;
; SUB_GOAL_FIND checks to see whether firing of a rule could accomplish
; a goal or sub-goal.  if so, the conditions of the rule are instantiated
; as sub-goals.
;
(defun sub_goal_find (rul)
; (my_print '"subgoal finding on " rul);   !
   ; initialize variables (see prob_fire.l)
   (mapcar 'delete_binding vbl_list)
   (prog (actns gls result)
      (setq actns (get rul 'actions))
      (setq result nil)
;    subgoal refraction:
      (cond ( (member rul (get (car active_problems) 'rules_sub_goaled))
              (return nil)
            )
      )
;    for  all actions:
      outloop
      (cond ( (null actns) (return result) ) )
      (setq gls (union  (get (car active_problems) 'sub_goals)
                        (get (car active_problems) 'goals)
                )
      )
;    for all sub-goals and goals:
         inloop
         (cond ( (null gls)
                 (setq actns (cdr actns))
                 (go outloop)
               )
         )
;       would action accomplish sub-goal?
         (cond ( (and (equal (caar actns) (caar gls))
                      (truth_compatible (car actns) (car gls))
                 )
;       if so, make the conditions into sub-goals
                 (bind (second (car actns)) (second (car gls)) )
                 (build_sub_goals (get rul 'conditions) (car actns) rul)
                 (put rul 'satisfies_goal? t)
                 (put (car active_problems) 'rules_sub_goaled
                      (cons rul (get (car active_problems) 'rules_sub_goaled))
                 )    ; refraction
                 (setq result t)
               )
          )
          (setq gls (cdr gls))
          (go inloop)
   )
)
;*****************************************************  36
; BUILD_SUB_GOALS constructs sub-goals out of conditions and instances.
;
(defun build_sub_goals (condns actn rul)
   (declare (special actn) (special rul))
   (mapcar '(lambda (condn)
             ; (my_print '"building subgoals from condition:  " condn)  ; !!!!
               (setq sub_g (list (car condn)
                                 (get_binding (second condn))
                                 (third condn)
                           )
               )
;             if subgoal is not satisfied already, add it to subgoals
               (cond ( (and (no_nils (second sub_g))  ; fully bound
                            (not (is_satisfied sub_g active_messages))
                       )
                       (put (car active_problems) 'sub_goals
                            (cons sub_g
                                  (get (car active_problems) 'sub_goals)
                            )
                       )
;                     activate concept from subgoal:
                       (put (car condn) 'activation
                            (max1
                                    (add .2 (get (car condn) 'activation))
                            )            ; arbitrary number
                       )
                       (setq goal_activated (cons (car condn) goal_activated))
                       ; if newly active,
                       ; note how activation occurred {for analogy}
                       (cond ( (not_member (car condn) active_concepts)
                               (my_print '"Activating concept " (car condn)
                                         '" by sub-goaling on " rul
                               )
                               (setq active_concepts (cons (car condn)
                                                           active_concepts
                                                      )
                               )                           
                               (put (car condn) 'goal_activated_by
                                    (remove-duplicates
                                       (cons (car actn) 
                                             (get (car condn) 
                                                  'goal_activated_by
                                             )
                                        )
                                     )
                               )
                             )
                        )
                )
             )
            )  ; end lambda
           condns
    )
)
;*****************************************************  37
; CLASSIFY classifies an object by setting a problem to be solved whose
; goal is a message with any predicate applying to the object with
; confidence greater than a confidence threshold.  OBSOLETE.
 
(defun classify (evidence object)
   (m_print '"---------------------------------------------")
   (my_print '"classifying " object)
   (setq prob_name (gensym 'classification))
   (intern prob_name)
   (make_problem evidence
                 (list (list '???? (list object) 'true ))
   )
   (solve_problem prob_name)
)
; END OF PROB_SPREAD.L
; FILE:        store.l
; programmer:  Paul Thagard
; purpose:     storing of messages in concepts.
;              storing of problem solutions.
; created:     1-6-85
; last update: 9-10-86
 

; *******************************************************
; UPDATE_MESS takes a revised message and stores it with the
; appropriate concept.  in the simplest case, the message is
; just the replacement of what is stored with the instances
; of the concept; but if projections are underway, it is
; necessary to search through the projected instances of the
; concept to find the appropriate storage place.
;
(defun update_mess (mess)
   (prog (store_places)
      (setq store_places (cons 'instances
                               active_projections
                         )
      )
      loop
      (cond ( (null store_places) (return nil) ) )
      (cond ( (replace_mess mess (car store_places))
              (return t)
            )
      )
      (setq store_places (cdr store_places))
      (go loop)
    )
)
; *************************************************************
; REPLACE_MESS checks if an older version of a message is in a
; given storage place and if so replaces it with the new version.
; the formula for the new confidence of a message is:
; <confidence of old message> + [(1 - <conf. of old mess.>) * <conf. of new>]
;  add:  handle contradictions and adjust confidence downwards.
;
(defun replace_mess (mess store_place)
   (setq found_mess (mess_on mess (get (car mess)
                                         store_place
                                  )
                             'found 
                    )
   )
   (cond (   found_mess
             (setq new_confidence
                   (add (get_confidence found_mess)    ; old confidence
                        (times (sub 1 (get_confidence mess))
                               (get_confidence mess)
                        )
                    )
             )
             (put (car mess) store_place
                  (cons (list (car mess) (second mess) (third mess)
                              new_confidence
                              (cond ( (fifth mess) (fifth mess))) ; mess-name
                        )
                        (remove found_mess
                                (get (car mess) 'store_place)
                        )
                  )
             )
         )
         (t (put (car mess) store_place
                 (cons mess (get (car mess) store_place))
            )
         )
    )
    found_mess
)
; ********************************************************
 
;
;  STORE_ACTIONS uses the information in an executed action
;  to add a new instance to the instance list of a concept.
;  if a projection is active, then the instance is stored on
;  the property list of the concept under the projection name
;  instead of instances.
;
(defun store_actions (actn)
 
;   if effector, start projection:    <<add:  handle move>>
    (cond ( (equal (fifth actn) 'effect)
            (start_projection (car actn))
            (setq actn (list (car actn) (second actn) (car (third actn))
                             (fourth actn) 
                             (cons (car active_projections)
                                   (second (third actn))
                             )
                       )    
            )
            (setq store_place (car active_projections))
          )
          ( t  (cond ( (listp (third actn)) ; projected truth value
                       ; store in most recent relevant projection:
                       (setq store_place (car (second (third actn))))
                       (setq actn (list (car actn) (second actn) 
                                        (car (third actn))
                                        (fourth actn) (second (third actn))
                                  )
                       )
                     )
                     (t (setq actn (remove (fifth actn) actn))
                        (setq store_place 'instances)
                     )
               )
          )
   )
;   store the appropriate message with its concept
    (replace_mess actn store_place)
)
; *******************************************************************
; STORE_PROBLEM stores a list of rules used and rules used in projections
; with a problem name; and it stores the problem name with relevant concepts,
; namely those mentioned in the starting conditions and goals.
(defun store_problem (prob_name)
   ; store rules:
   (put prob_name 'rules_used
                   (union (get prob_name 'rules_used)
                          (union_map 'get_projected_rules 
                                     active_projections
                          )
                   )
   )
   ; store projecting rules:
   (put prob_name 'projecting_rules (projecting_rules prob_name))             
   ; associate problem with key concepts:
   (mapcar 'put_solution (key_concepts_from prob_name))
   ; associate concepts with problem
   (put prob_name 'attached_concepts (key_concepts_from prob_name)) 
)
; ****************************************************************
; CONC_FROM_PROB takes concepts from the
; specification of a problem.
(defun conc_from_prob (prob)
   (concepts_from (union (get prob 'start)
                         (get prob 'goals) 
                  )
   )
)
; ****************************************************************
; KEY_CONCEPTS_FROM ignores "generic" concepts that are less
; informative because they are so universal, e.g. spatial concepts.
(defun key_concepts_from (prob)
   (exclude generic_concepts (conc_from_prob prob))
)
; ****************************************************************
; GET_PROJECTED_RULES returns the rules used for a particular projection
; in a problem.  Like projecting_rules, this is awkward, and should not
; depend on car active_problems.
(defun get_projected_rules (projn)
   (get (car active_problems) projn)
)
; PUT_SOLUTION has the same flaw.
(defun put_solution (struc)
   (put struc 'old_solutions
              (cons (car active_problems) 
                    (get (car active_problems) 'old_solutions)
              )
   )
                   
)
 ;***************************************************************************
; UNSTORE simply deletes a stored message.
; <<Not used>>.
(defun unstore (mess store_place)
   (put (car mess) 'store_place
        (remove mess (get (car mess) store_place))
   )
)
; end of store.l; FILE:         theory.l
; PURPOSE:      Theory evaluation in PI.
; PROGRAMMER:   Paul Thagard
; CREATED:      10-9-85
; LAST UPDATE:  2-12-86
; ***************************************************************
; STORE_EXPLN stores what explains what, and triggers an attempt at
; inference to the best explanation.  It is called:
;   (1) by abduce_fact in explain.l, when explanation of a fact is
;           produced by abduction to a fact;
;   (2) by explain and store_all_explns in explain.l
;           when explanation of a rule is
;           produced with the help of a rule produced by abductive
;           generalization.
(defun store_expln (hypoth explanandum)
    
    (put hypoth 'explains (cons explanandum 
                                (get hypoth 'explains)
                          )
    )
    (put explanandum 'explainers (cons hypoth
                                       (get explanandum 'explainers)
                                 )
    )
    ; if hypothesis explains at least two facts, evaluate it:
    (cond ( (greaterp (length (get hypoth 'explains)) 1)
            (best_explanation? hypoth)
          )
    )
    hypoth ; return name of hypothesis
)
; ********************************************************************
; BEST_EXPLANATION? determines whether a theory is the best explanation
; compared to other available explanations in the same domain.
; Note, it evaluates theories of any kind, as long as they are represented
; by structures that include a list of explananda, each of which includes
; a list of explainers.  Most simply, this can be used to evaluate simple
; hypotheses of the form Fa, or rules, of the form (x)(Fx->Gx).  
; Uses global variables:  competitors, evidence, best_exp, tie_flag.
(defun best_explanation? (hypoth)
   (setq evidence nil)  ; evidence set up by find_competitors
   (setq tie_flag nil)  
   ; find the competitors of hypoth, not co-hypotheses
   (setq competitors (exclude (get hypoth 'co-hypotheses)
                              (find_competitors hypoth)
                     )
   )
   (setq all_co-hypotheses (union_map 'get_co-hyp competitors))
   ; pick the best competitor
   ( setq best_exp (best_exp_of competitors ))
   ; announce:
   (cond ( trace_data
           (my_print '"The best explanation is: " best_exp )
           (cond ( (equal (get best_exp 'data_type) 'hypothesis)
                   (my_print '"                   "(get best_exp 'message))
                 )
           )
           (my_print best_exp '" explains: " 
                     (remove_duplicates (get best_exp 'explains))
           )
           (my_print '"Competing hypotheses: "  competitors)
           (my_print '"Co-hypotheses: " (get best_exp 'co-hypotheses))
           (my_print '"Total evidence: " evidence)
           (cond ( tie_flag
                   (my_print '"Tied hypotheses: " tie_flag)
                 )
           )
         )
   )
   ; increase confidence/strength of best_exp, and decrease others.
   (adjust_conf best_exp competitors)
)
; ***********
(defun get_co-hyp (hyp)
    (get hyp 'co-hypotheses)
)
; ********************************************************************
; FIND_COMPETITORS finds all the competitors of a hypothesis. 
; A competitor is,
; at first approximation, a hypothesis that explains something that
; the original does.  The relation is transitive: if T1 explains
; E1 which is explained by T2 which explains E2 which is explained by
; T3, T1 and T3 should be competitors.  This function gets the entire set.
(defun find_competitors (hyp)
   (prog (new_evid compet)
      (setq all_compet (list hyp))
      (setq new_compet nil)
      (setq new_evid (get hyp 'explains))
      loop
      (setq evidence (union evidence new_evid))
      (cond ( (null new_evid) 
              (setq evidence (remove_duplicates evidence))               
              (return (remove_duplicates all_compet))
            )
      )
      ; add hypotheses that explain evid
      (setq new_compet (union_map 'get_explainers new_evid))
      ; ignore ones already checked:
      (setq new_compet (exclude all_compet new_compet))
      ; add to all competitors:
      (setq all_compet (union all_compet
                              new_compet
                       )
      )
      ; add to evidence the explananda of the new hypotheses
      (setq new_evid (exclude evidence
                              (explananda_of_list new_compet)
                     )
      )
      (go loop)
   )
) 
; ************************************************************
; trivial functions just used:
(defun explananda_of_list (lst)
   (remove_duplicates (union_map 'get_explananda lst))
)
(defun get_explananda (hyp)
   (get hyp 'explains)
)
(defun get_explainers (explanandum)
   (get explanandum 'explainers)
)
; ************************************************************
; BEST_EXP_OF picks the best explanation out of a set of competitors.
(defun best_exp_of (lst)
   (prog (compets best_so_far)
       (cond ( (null lst) (return null)))
       (setq best_so_far (car lst))
       (setq compets (cdr lst))
       loop
       (cond ( (null compets) (return best_so_far)))
       (cond ( ( equal (better_expln (car compets) best_so_far )
                       (car compets)
               )
               (setq best_so_far (car compets))
             )
       )
       (setq compets (cdr compets))
       (go loop)
   )
)
; *********************************************************************
; BETTER_EXPLN determines if one hypothesis is better than another,
; considering consilience (number of facts explained) and
; simplicity:  (number of co-hypotheses required).
; It first looks for a decisive qualitiative 
; answer, then for a more subjective quantitative one.
(defun better_expln (hyp1 hyp2)
   (or (better_expln_qual hyp1 hyp2)
       (better_expln_quant hyp1 hyp2)
   )
)
; ********************************************************
; BETTER_EXPLN_QUAL qualitatively determines the best explanation,
; using subset relations rather than metrics, resulting in more ties.
(defun better_expln_qual (hyp1 hyp2)
    (cond ( (and (is_tie (more_consilient hyp1 hyp2))
                 (null (is_tie (simpler hyp1 hyp2)))
            )
            (simpler hyp1 hyp2)
          )
          ( (equal (more_consilient hyp1 hyp2) hyp1)
            (cond ( (or (equal (simpler hyp1 hyp2) hyp1)
                        (is_tie (simpler hyp1 hyp2))
                    )
                    hyp1
                  )
            )
         )
         ( (equal (more_consilient hyp1 hyp2) hyp2)
           (cond ( (or (equal (simpler hyp1 hyp2) hyp2)
                       (is_tie (simpler hyp1 hyp2))
                   )
                   hyp2
                )
          )
        )
        (t nil)
   )
)
; **********************************************
(defun note_tie (hyp1 hyp2)
   (setq tie_flag (cons (list hyp1 hyp2) tie_flag))
   hyp1  ; return hyp1 to keep comparison going.
)
(defun is_tie (result)
   (equal result 'tie)
)
; ***********************************************
; MORE_CONSILIENT determines whether a hypothesis explains more facts,
; or more consilient facts, than its competitors.
(defun more_consilient (hyp1 hyp2)
   (cond ( (equal (get hyp1 'explains)
                  (get hyp2 'explains)
           )
           'tie
         )
         ( (subset (get hyp1 'explains)
                   (get hyp2 'explains)
           )
           hyp2
         )
         ( (subset (get hyp2 'explains)
                   (get hyp1 'explains)
           )
           hyp1
         )
         (t nil)
   )
)
; *********************************************************
; SIMPLER compares simplicity on the basis of the number of
; co-hypotheses.
; This must be stated in such a way that a hypothesis that does
; not explain anything is not automatically the simplest.
; So look at simplicity relative to amount explained:
; Simplicity = 1 - ( co-hypotheses / ( facts explained X all co-hypotheses))
(defun simpler (hyp1 hyp2)
   (cond ( (equal (simplicity hyp1) (simplicity hyp2))
           'tie
         )
         ( (greaterp (simplicity hyp1)
                     (simplicity hyp2)
           )
           hyp1
         )
         ( t hyp2)
   )
)
; *********************************************************
; SIMPLICITY calculates simplicity in terms of
; explananda per co-hypothesis.
; Simplicity decreases with the number of co-hypotheses used,
; but decreases with the number of facts explained.  To
; get a 0 ... 1 metric, simplicity also decreases with the
; total number of co-hypotheses.
; This could be weighted. 
(defun simplicity (hyp)
   (put hyp 'simplicity
        (cond ( (null (get hyp 'co-hypotheses)) 1)
              ( (null (get hyp 'explains)) 0)
              ( t (diff 1 (quotient (float (length (get hyp 'co-hypotheses)))
                                    (plus (float (length (get hyp 'explains)))
                                          (float (length all_co-hypotheses))
                                     )
                          )
                  )
              )
         )
      
   )
)
; *********************************************************
; MOST_IMPORTANT returns the hypothesis that explains the most 
; important facts, by adding up the total importance of the facts
; explained.  Note:  importance ranges from 0 .. 1.
; If the fact to be explained is an ordinary message, its importance
; is the degree of activation of the concept to which it is attached.
; If it is a rule that was explained, the importance is its strength.
(defun most_important (hyp1 hyp2)
    (compute_importances hyp1)
    (compute_importances hyp2)
    (put hyp1 'total_imp 
              (apply 'add (mapcar 'get_importance (get hyp1 'explains)))
    )  
    (put hyp2 'total_imp
              (apply 'add (mapcar 'get_importance (get hyp2 'explains)))
    )
    (cond ( (equal (get hyp1 'total_imp)
                   (get hyp2 'total_imp)
            )
            'tie
          )
          ( (greaterp (get hyp1 'total_imp)
                      (get hyp2 'total_imp)
            )
            hyp1
          )
          (t hyp2)
   )
)
; ********************************************************************
(defun get_importance (atm) 
   (get atm 'importance)
)
; ********************************************************************
; COMPUTE_IMPORTANCES ensures that each of the explananda has an
; attached importance, taken from strength or activation.
(defun compute_importances (hyp)
   (cond ( (equal 'rule (get hyp 'data_type))
           (mapcar 'imp_rule (get hyp 'explains))
         )
         ( (equal 'hypothesis (get hyp 'data_type))
           (mapcar 'imp_fact (get hyp 'explains))
         )
         ( t (mapcar 'imp_default (get hyp 'explains)))
   )
)
; *****************************************************************
; trivial functions in the above:
(defun imp_rule (rul)
    (put rul 'importance (get rul 'strength))
)
(defun imp_fact (fact)        ; activation of concept fact belongs to
    (put fact 'importance 
              (get (get_predicate (get fact 'message))
                   'activation
              )
    )
)
(defun imp_default (x)
   (put_if_needed x 'importance 1)
)
;  add only if no value is already there:
(defun put_if_needed (atm place value)
   (cond ( (null (get atm place))
           (put atm place value)
         )
   )
)
; **********************************************************
; BETTER_EXPLN_QUANT integrates the consideration of consilience
; and simplicity by making them both numerical values.
; consilience (t) = # of facts t explains/ # of total relevant facts.
; simplicity (t) = 1- (# of co-hypotheses of t/ # total co-hypotheses
;                                               X # facts explained)
; Note that these are both relative to evidence and competitors set up
; in best_explanation?
(defun better_expln_quant (hyp1 hyp2)
   (compute_importances hyp1)
   (compute_importances hyp2)
   (put hyp1 'expln_value (compute_expln hyp1))
   (put hyp2 'expln_value (compute_expln hyp2))
   (cond ( (equal (get hyp1 'expln_value)
                  (get hyp2 'expln_value)
           )
           (note_tie hyp1 hyp2)
         )
         ( (greaterp (get hyp1 'expln_value)
                     (get hyp2 'expln_value)
           )
           hyp1
         )
         (t hyp2)
    )
)
; ************************************************************
; COMPUTE_EXPLN returns a number indicating the explanatory value of a
; hypothesis.
(defun compute_expln (hyp)
   (times (simplicity hyp) (consilience_imp hyp))
)
   
; ***********************************************************
; CONSILIENCE_IMP measures not only the amount of facts 
; explained, but also how important they are.
(defun consilience_imp (hyp)
   (put hyp 'consilience_imp
       (quotient (total_importance (get hyp 'explains))
                 (total_importance evidence)
       )
   )
)
; ******************************************
; TOTAL_IMPORTANCE 
(defun total_importance (lst_of_explananda)
   (apply 'add (mapcar 'get_importance lst_of_explananda))
)
; *****************************************
; ADJUST_CONF increase the confidence of the best explanation and decreases
; that of the ones it beat.  Global:  hyp_msg
; <<ADD:  more principled adjustments, and update message list and instnaces.
(defun adjust_conf (best_hyp others)
   (setq hyp_msg (get best_hyp 'message))
   (cond ( hyp_msg
           (put best_hyp 'message 
                (list (car hyp_msg) (second hyp_msg) (third hyp_msg)
                      (up_conf (fourth hyp_msg)) (fifth hyp_msg)
                )
           )
           (mapcar 'down_conf others)
          )
    )
)
;  arbitrary increase in confidence:  might make this proportional to 
;  number of facts explained, degree of simplicity, and number of 
;  explanations defeated.
(defun up_conf (num)
    (my_max 1 (add num .2))
)
(defun down_conf (hyp)     ; global:  msg
    (setq msg (get hyp 'message))
    (put hyp 'message
         (list (car msg) (second msg) (third msg) 
               .1
               (fifth msg)
         )
    )
)
; ****************************************************************
; END of theory.l
     

; FILE:             trig.l
; PROGRAMMER:       Paul Thagard
; PURPOSE:          Triggering conditions for inference in PI
; CREATED:          8-6-84
; LAST UPDATE:      12-2-86
; **********************************************************
; constants used in triggering:
; infer_threshold is a constant which indicates a minimum level of
; activation or support required for various inferences to be made.
  (setq infer_threshold .5)
;
; analogy_threshold determines goodness of  match between the
; concepts of the current problem and a stored problem.
  (setq analogy_threshold 3)
; **********************************************************
; global variables for triggering:
;    abd_triple - information used in abduction:
;              (<explanandum> <explaining rule> <condition to abduce>)
(setq abd_triple nil)
;    common_relations - used for generalizing about relations
;               - set by get_common_concepts
; **********************************************************
 
;  TRIGGER is called by solve_problem.  it monitors the current state
;  of the system - active concepts, rules, and messages - and
;  determines whether various kinds of inductive inference should
;  be made.  these include:
;        1.  generalization (instance-based)
;        2.  generalization (condition-based)
;        3.  specialization  (done by check in gen.l)
;        4.  bottom-up concept formation
;        5.  conceptual combination
;        6.  abduction to facts
;        7.  abduction to rules
(defun trigger ()
   (cond (trace_prob (my_print '"Triggering inductions ...")))
;  identify concepts with common instances:
   (setq common_concepts (get_common_concepts))
 
;  trigger instance-based generalization and conceptual combination:
   (cond ( common_concepts (mapcar 'trig_gen_comb common_concepts)))
 
;  trigger generalization involving relations:
;  <<this needs to be more selective, counting instances.>>
;  (cond ( common_relations (mapcar 'gen_long common_relations) ) )
 
;  trigger condition-based generalization:
   (setq common_rules (mapcar 'get_common_rules
                              (common_action active_rules)
                      )
   )
   (mapcar 'trig_cond_gen common_rules)
 
; trigger specialization
;    - see check in gen.l  If there is
;      an active rule with conditions satisfied but action false, then
;      add a new rule with conditions supplemented by a message
;      concerning something "unusual" about the same object.
 
; trigger abduction
   (cond ( (get (car active_problems) 'explan_status) ; expln. context
            ;abduction to fact:
            (trig_abduce)
            ;  abduction to rule 
            (trig_abd_gen)   ; see explain.l
         )
    )
;  trigger formation of new concepts from active rules with the
;  same set of at least 2 conditions, i.e. from a&b&c -> d and a&b&c -> d
;  form the new concept a_b_c.
   (mapcar 'form_concept_from_rules              ; these functions ar
           (rules_with_same_condn active_rules)  ; in pi.conc
   )
 
)  ; end trigger
 
; ********************************************************
; TRIG_GEN_COMB  triggers generalization and conceptual combination,
; using lists of concepts collected by get_common_concepts.  the
; triples have structure ( concept1 concept2 vbl? ) where vbl?
; is t or nil depending on whether the instance which
; the concepts had in common was a universal variable $x.
 
(defun trig_gen_comb (triple)
   (cond ( (and (more_active_than (car triple) infer_threshold)
                (more_active_than (second triple) infer_threshold)
           )
;          both concepts are highly active so:
           (generalize triple)
           (generalize (list (second triple) (car triple) (third triple)))
           (combine (car triple) (second triple))
         )
   )
)
; ********************************************************
;  TRIG_COND_GEN triggers condition-based generalization using list
;  collected by get_common_rules, consisting of quadruples:
;  (rule1  rule2  action_to_gen  condn_to_gen).
 
(defun trig_cond_gen (quadruple)
   (cond ( (null quadruple) nil)       ; ignore if null quadruple
;        generalize from well-supported rules:
         ( (and (more_active_than (car quadruple) infer_threshold)
                (more_active_than (second quadruple) infer_threshold)
            )
            (condn_gen (car quadruple) (second quadruple)
                       (third quadruple) (fourth quadruple)
            )
         )
    )
)
; ********************************************************
; MORE_ACTIVE_THAN checks that the activation of a structure is more
; than a given threshold
;
(defun more_active_than (struc thresh)
   (> (get struc 'activation) thresh)
)
; **********************************************************
;  GET_COMMON_CONCEPTS searches through the message list for instances
;  of concepts in common, e.g. for concepts a and b which both have object
;  o as instances.   Algorithm:  for each message, see if any of the
;  rest of the messages have the same instances.  Returns a list of
;  triples, (concept1 concept2 vbl?).
;
(defun get_common_concepts ()
   (prog (messages first_mess others result)
      (setq messages active_messages)
      (setq common_relations nil)
      ;E(cond ( (get (car active_problems) 'explan_status)
      ;E         (setq messages (union messages
      ;E                              (get (car active_problems) 'goals)
      ;E                       )    ; if problem is an explanation,
      ;E        )                   ; include the goals to be explained
      ;E      )
      ;E)
    
      (setq result nil)
      outloop
      (setq first_mess (car messages)
            others (cdr messages)
      )
      (cond ( (null others) (return result) ))
;       see if first message has common instances with rest
        inloop
        (cond ( (null others)
                (setq messages (cdr messages))
                (go outloop)
              )
        )
        (cond ( (and (equal (second first_mess) (second (car others)) )
                     (not_equal (car first_mess) (car (car others)))
                     ; ignore if both messages are projected:  <kluge for c.c.>
                     (not (and (equal (third first_mess) 'proj_true)
                               (equal (third  (car others)) 'proj_true)
                          )
                     )
                )
                (setq result (cons (list (car first_mess)
                                         (car (car others))
                                         (is_variable (car (second first_mess) )) ;  ideally, should check all instances
                                    )
                              result
                              )
                )
              )
        )
        ; look for relational connections too:
        ; note:  the following conditions are too loose:
        (cond ( (and (greaterp (length (append (second first_mess)
                                               (second (car others))
                                       )
                               )
                               2
                      )  ; at least one n-ary relation
                      (intersect (second first_mess)
                                 (second (car others))
                      )
                )
                (setq common_relations
                      (cons (list (list first_mess)
                                  (list (car others))
                            )
                            common_relations
                      )
                 )
           )
        )
        (setq others (cdr others))
 
        (go inloop)
    )
)
; *********************************************************
; GET_COMMON_RULES starts with two rules with a common action
; and looks to see if they have a common condition which is
; generalized.  e. g. :
; a & b -> c,  a & d -> c, so a -> c.  takes candidates got from
; common_action, having the form (rule1 rule2 action_to_gen),
; and returns the same list with condn_to_gen added to the end.
;
(defun get_common_rules (candidates)
   (prog (r1_condns r2_condns r1_first r2_first result)
      (setq r1_condns (get (car candidates) 'conditions))
;     for each condition of r1:
      outloop
      (cond ( (null r1_condns) (return nil) ) )
      (setq r2_condns (get (second candidates) 'conditions))
      (setq r1_first (car r1_condns))
;        for each condition of r2:
         inloop
         (cond ( (null r2_condns)
                 (setq r1_condns (cdr r1_condns) )
                 (go outloop)
               )
         )
         (setq r2_first (car r2_condns))
         (cond ( (equal (car r1_first) (car r2_first) )
                  (return (list (car candidates)
                                (second candidates)
                                (third candidates)
                                r1_first
                           )
                  )
               )
         )
         (setq r2_condns (cdr r2_condns))
         (go inloop)
   )
)
; *********************************************************
; COMMON_ACTION searches through a list of rules for two rules with the
; same action, returning a list of those rules plus the action in
; common:  (rule1 rule2 action_to_gen).
; only looks at first action of actions of a rule.
;
(defun common_action (rules)
   (prog (rule_list first_rul others result)
      (setq rule_list rules
            result nil
      )
      outloop
      (setq first_rul (car rule_list)
            others (cdr rule_list)
      )
      (cond ( (null others) (return result) ))
 
;       see if first rule matches up with any rule
        inloop
        (cond ( (null others)
                (setq rule_list (cdr rule_list))
                (go outloop)
              )
        )
        (cond ( (equal (car (get first_rul 'actions) )  ; not general
                       (car (get (car others) 'actions) )
                )
                (setq action_to_gen (car (get first_rul 'actions) ))
                (setq result
                      (cons (list first_rul (car others) action_to_gen) result)
                )
              )
        )
        (setq others (cdr others))
        (go inloop)
    )
)
; *********************************************************
; CONDN_GEN does a condition-based generalization, using condn_to_gen
; the condition predicate got from get_common_rules, and action_to_gen,
; the action predicate got from common_action.
(defun condn_gen (rule1 rule2 action_to_gen condn_to_gen)
   (setq concpt (car condn_to_gen)
         actn_concpt (car action_to_gen)
         stren (min (get rule1 'strength)
                    (get rule2 'strength)
               )
   )
;  make rule:
   (setq gen_result              ; check for redundancy
         (make_rule concpt concpt actn_concpt 'blank 'default stren)
   )
   (cond ( (and trace_prob gen_result)
           (my_print '"condition-based generalization from "
                     (list rule1 rule2) '" to " concpt '" --> " actn_concpt
           )
         )
   )
;  activate concept:
   (cond ( gen_result
           (setq active_concepts (cons concpt active_concepts))
           (put concpt 'activation stren)                     ; kluge
         )
   )
)
; *********************************************************
 
;  trig.l





;  FILE         K9U9:PI.WORLD
;  PROGRAMMER:  Paul Thagard
;  Purpose:     Creation of simulated environment.
;  Created:     5-20-85
;  Last update: 5-20-85
;
;  WORLD is an N X N grid, with messages stored at each
;  entry corresponding to what would be observed at that
;  point in the grid.
;  Global variables:  X_COORD:  x coordinate.
;                     Y_COORD:  y coordinate.
;  Possible directions are NORTH, SOUTH, EAST, WEST,
;  with movement changing the values of the coordinates.
;
(SETQ WORLD_DEBUG T)
 
;********************************************************
(PROGN
;********************************************************
; MAKE_WORLD (N) sets up an N X N grid and establishes an
; initial location in the middle.
;
(DEFUN MAKE_WORLD (SIZE)
   (DEFINE (WORLD ARRAY (SIZE SIZE) ))   ; make grid.
   (SETQ  WORLD_MADE T)                 ; flag
   (SETQ X_COORD (IDIVIDE SIZE 2))
   (SETQ Y_COORD (IDIVIDE SIZE 2))
   (SETQ WORLD_SIZE SIZE)
   (MY_PRINT '"World made of size " SIZE)
)
;*********************************************************
;  OBSERVE adds to the list of active messages those messages
;  available through observation at a particular place in the
;  world.
(DEFUN OBSERVE ()
   (COND ( WORLD_MADE
           (SETQ ACTIVE_MESSAGES
                 (UNION ACTIVE_MESSAGES
                        (WORLD X_COORD Y_COORD)
                 )
           )
         )
    )
)
;**********************************************************
; MOVE_SYSTEM takes the information from an effector MOVE
; and relocates the system in the world appropriately, moving
; the appropriate number of steps in a given direction.
(DEFUN MOVE_SYSTEM (DIRECTION STEPS)
   (COND ( (EQUAL DIRECTION 'NORTH)
           (SETQ X_COORD (ADD X_COORD STEPS))
         )
         ( (EQUAL DIRECTION 'SOUTH)
           (SETQ X_COORD (SUB X_COORD STEPS))
         )
         ( (EQUAL DIRECTION 'EAST)
           (SETQ Y_COORD (ADD Y_COORD STEPS))
         )
         ( (EQUAL DIRECTION 'WEST)
           (SETQ Y_COORD (SUB Y_COORD STEPS))
         )
    )
   ;  Keep the system from falling off the grid:
   (COND ( (LESS X_COORD 1) (SETQ X_COORD 1) )
         ( (GREATER X_COORD WORLD_SIZE) (SETQ X_COORD WORLD_SIZE) )
   )
   (COND ( (LESS Y_COORD 1) (SETQ Y_COORD 1) )
         ( (GREATER Y_COORD WORLD_SIZE) (SETQ Y_COORD WORLD_SIZE) )
   )
   (COND ( WORLD_DEBUG (DESCRIBE_WORLD) ))
)
;***************************************************************
;  ADJUST keeps the system from falling off the grid, by ensuring
;  the x and y coordinates never get too big or small.
;
(DEFUN ADJUST (COORD)
   (COND ( (LESS COORD 0) (SETQ COORD 0) )
         ( (GREATER COORD WORLD_SIZE) (SETQ COORD WORLD_SIZE) )
   )
)
;******************************************************************
(DEFUN DESCRIBE_WORLD ()
  (MY_PRINT '"X coordinate: " X_COORD '" Y coordinate: " Y_COORD
            '" Messages: " (WORLD X_COORD Y_COORD)
  )
)
;******************************************************************
(PRINT '"PI.WORLD loaded.")
                                  ;  end PROGN
;*****************************************************; FILE:         wts.l
; PURPOSE:      discovery and evaluation of wave theory of sound
; PROGRAMMER:   Paul Thagard
; CREATED:      9-30-86
; UPDATED:      12-1-86
(run 15)
(clear_all)
(setq print_to_file nil)
(setq analogy_flag nil)
(my_print '"***********************************************")
(my_print '"Running PI with input data/wts.l.")
(my_print '"Problem:  How to explain properties of sound?")
(defun lf () (load "prob_spread.l"))
(defun ld () (load "wts.l"))
(setq trace_data t)
(setq trig_analog nil)
; **************************************************************
; Concepts:
(make_concept_s '(sensation physical_phenomenon voice music whistle bang
                  entertainment singing device jump is_heard goes_through_air
                  near hears echoes is_obstructed spread_plane swell
                  has_crest vibrate movement 
                  spread_spherically spread_plane thing plays instrument
                  pass_through lyre_music flute_music  lyre change
                 )
)
(make_concept 'sound 
              '(sensation physical_phenomenon)
              '(voice music whistle bang)
              nil nil 0
)
(make_concept 'propagate '(motion) nil nil nil 0)
(make_concept 'reflect '(motion_back) nil nil nil 0)
(make_concept 'motion '(change)
                      '(propagate reflect pass_through) nil nil 0
)
(make_concept 'pass_through '(motion) nil nil nil 0)
(make_concept 'music '(sound entertainment) '(instrumental_music singing)
              nil nil 0
)
(make_concept 'instrumental_music '(music) '(lyre_music flute_music)
              '( (instrumental_music (obj_a) true))
              nil 0
)
(make_concept 'instrument '(device) '(stringed_instrument) 
              nil nil 0
)
(make_concept 'stringed_instrument '(instrument) '(lyre)
              '( (stringed_instrument (obj_b) true))
              nil 0
)
(make_concept 'move_up_down '(movement) '(wave jump) 
              nil nil 0
)
(make_concept 'wave '(movement) '(water_wave hand_wave) nil nil 0)	      
(make_concept 'motion_back '(motion) '(reflect bounce) nil nil 0)
(make_concept 'bounce '(motion_back) nil '((bounce (obj_c) true))
              nil 0
)

; **************************************************************
; Rules about sound:
; R0:  Anything heard is a sound.
(make_rule 'is_heard  'is_heard 'sound 'result 'actual 1)
; R1:  sounds are transmitted by air.
(make_rule 'sound 'sound 'goes_through_air 'transmission 'default .8)
; R2:  sounds are heard by persons near them.
(make_rule_long 'sound 
                '( (sound ($x) true) (person ($y) true) (near ($x $y) true))
                '( (hears ($y $x) true))
                'effect
                'default
                .7
)
; R3:  obstructed sounds echo.
(make_rule_long 'sound
                '( (sound ($x) true ) (is_obstructed ($x) true) )
                '( (echoes ($x) true))
                'obstruction_result
                'default
                .4
)
; R4:  sounds spread spherically.
(make_rule 'sound 'sound 'spread_spherically 'spread_shape 'default .9)
; *******************************************************
; Rules about waves:
; R5:  Waves spread in a plane.
(make_rule 'wave 'wave 'spread_plane 'spread_shape 'default .7)
; R6:  Waves are swells.
(make_rule 'wave 'wave 'swell 'motion_shape  'default .6)
; R7:  Waves propagate.
(make_rule 'wave  'wave 'propagate 'motion 'default .8)
; R8:  Waves have crests.
(make_rule 'wave 'has_crest 'shape 'motion 'default .8)
; R9:  Waves reflect.
(make_rule_long 'wave
                '((wave ($x) true) )
                '((reflect ($x) true))
                'obstruction_effect
                'default
                .6
)
; R10:  Waves pass through each other.
(make_rule 'wave 'wave 'pass_through 'motion 'default .9)
; ***********************************************************
; R11:  Balls propagate.
(make_rule 'ball 'ball 'propagate 'motion 'default .9)
; R12:  Balls reflect.
(make_rule 'ball 'ball 'reflect 'motion 'default .8)

; ***********************************************************
;  Miscellaneous rules.
; R13:  Music is pleasant.
(make_rule 'music 'music 'pleasant 'affect 'default .5)
; R14:  Instruments are delicate.
(make_rule 'instrument 'instrument 'delicate 'quality 'default .6)
  
; ***********************************************************
; Rules for associating from sounds to waves:
; R15:  Instrumental music is played by instruments.
(make_rule_long 'instrumental_music
                '( (instrumental_music ($x) true))
                '( (instrument (%y) true) (plays (%y $x) true))
                'method
                'actual
                1
)
                 
; R16:  Stringed instruments vibrate.
(make_rule 'stringed_instrument 'stringed_instrument 'vibrate 'movement 
           'default .7
)
; R17:  To vibrate is to move up and down.
(make_rule 'vibrate 'vibrate 'move_up_down 'move_shape 'default .8)


; ***********************************************************
; Rule to associate reflect -> ball.
; R18:  Bouncing is  done by balls.
(make_rule_long 'bounce
                '((bounce ($x) true))
                '((ball ($x) true) )
                'performer
                'default
                .6
)
                        
; ***********************************************************
(setq trace_data t)
; ***********************************************************
(make_problem 'sound_reflect
              '( (sound ($x) true))
              '( (propagate ($x) true)
                 (reflect ($x) true)
                 (pass_through ($x) true)
               )
              'explanandum
)
(put 'sound_reflect 'explan_status 'explanation)
(setq activated_last_time nil)
(solve_problem 'sound_reflect)

