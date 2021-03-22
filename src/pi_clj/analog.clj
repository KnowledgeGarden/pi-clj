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
(defn trig_analog (prob problem_list)
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
(defn analogize (base target)
   
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
(defn trace_concepts (base target)
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
(defn find_act_origins (conc base target)
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
(defn direction_find_origins (conc base target direction)
   (prog (still_to_expand first_conc activ_prop expanded result)
      (if activn_debug (my_print '&quot;Debugging &quot; conc '&quot; &quot; direction))
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
(defn same_arg_size (conc1 conc2)
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
; Example:  (pair_up 'a '(b c d) '(c d)) -&gt; ( (a c) (a d))
(defn pair_up (conc list1 list2)
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
(defn trace_objects (list_of_concept_pairs base target)
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
(defn pair_obj_up (concpt1 concpt2 prob1 prob2)
    (make_pairs (objects_from concpt1 prob1)
                (objects_from concpt2 prob2)
    )
)
; ********************************************************
; OBJECTS_FROM returns a list of objects associated with a 
; concept in the given problem.
(defn objects_from (conc prob)
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
(defn mess_from_prob (prob)
    (union (get prob 'goals)
           (get prob 'start)
    )
)
; **************************************************************
; MAKE_PAIRS takes two lists, and returns a list of pairs,
; with the nth atom of list1 paired with the nth of list2.
(defn make_pairs (lst1 lst2)
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
(defn get_effectors (prob)
   (get prob 'effects_objs)
)
; ****************************************************************
; PRINT_ANALOGY announces the found analogy.
(defn print_analogy (base target ana_conc ana_obj effects)
   (cond ( trace_prob
           (my_print '&quot;Analogy found between &quot; base &quot; and &quot; target )
           (my_print '&quot;Analogous concepts: &quot; ana_conc)
           (my_print '&quot;Analogous objects:  &quot; ana_obj)
           (my_print '&quot;Key effectors:      &quot; effects)
           (my_print '&quot;Activating rules:   &quot; (get base 'rules))
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
; &lt;&lt;Major weakness:  should do more analysis to figure out what are the 
;   responsible effectors or hypotheses.&gt;&gt;
(defn reconstruct (base target effects hypotheses ana_concs ana_objs) 
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
	      (my_print '&quot;New sub-goal:  &quot; new_sub_goal)
            )
      )
      (setq effs (cdr effs))
      (go loop)
   )
)
; *************************************************************
; FIND_ASSOCIATES takes a list of objects, and returns a list of
; their associates, based on an association list.
(defn find_associates (lst assoc_lst)
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
; &lt;&lt;Should screen hypotheses to rule out ones that were superceeded
;   by other members of the set that proved to be better explanations.&gt;&gt;
(defn reconstruct_hyps (base target hypoths ana_concs ana_objs)
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
(defn tight_analog_hypoth (base target hyp ana_concs ana_objs)
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
(defn circular (mess base target)
   (cond ( (mess_on mess (get target 'goals) 'sought)
           (my_print '&quot;Circular hypothesis rejected: &quot; mess)
           (my_print '&quot;Failed analogy: &quot;  base)
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
(defn loose_analog_hypoth (hyp ana_concs ana_objs)
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
(defn find_loose_associates (lst assoc_lst)
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