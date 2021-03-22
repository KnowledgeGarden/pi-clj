(ns pi-clj.prob_fire
  (:gen-class))

;  PURPOSE:     Problem solving in PI:  rule firing

;********************************************************************* 13
;  FIRE_RULES () fires the best of the active_rules, putting their
;  instantiated actions on the message list.
 
(defn fire_rules ()
    (declare (special best_rules) )
;   evaluate all the active rules
    (mapcar 'evaluate active_rules)
;   select the best rules
    (setq best_rules (reverse (select_rules max_rules)))
;   execute the actions of the best rules
    (cond ( trace_prob
            (my_print '&quot;FIRING RULES:  &quot; best_rules)
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
 
(defn select_rules (num)
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
(defn update_effects (rul)
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
 
(defn no_effector_conflict (rul effect_list)
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
(defn eff_conflict (effect effect_list)
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
(defn check_conflict (eff1 eff2)
    (member (list eff1 eff2) effector_conflicts)   ; set by data
)
; *****************************************************************15
; NOT_REDUNDANT checks that a rule has not already been fired with a given
; set of matching instances.
 
(defn not_redundant (rul)
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
 
(defn evaluate (rul)
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
(defn delete_binding (vbl)
   (put vbl 'binding nil)
)
;******************************************************************* 18
;  MATCH checks for a  match between a condition and a message,
;  binding up the variables in the condition.
 
(defn match (condn message rul )
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
; &lt;&lt;bug:  will screw up if there are two conditions with same predicate,
;   e.g. (planet ($x)) and (planet ($y) ).  Can't deal with identities.&gt;&gt;
(defn bind (arg_list1 arg_list2 )
   (prog (list1 list2 arg1 arg2)
         (setq list1 arg_list1
               list2 arg_list2
         )
         (cond ( (not (equal (length list1) (length list2)))
                 (my_print '&quot;Error:  wrong number of arguments &quot; 
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
(defn get_binding (arg_list)
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
 
(defn is_variable (arg)
   ( or (atom_begins arg #\$)        ; universal variable
        (atom_begins arg #\%)        ; existential variable
        
   )
)
;*********************************************************************** 22
; TRUTH_COMPATIBLE:  moved to misc.l
;*********************************************************************** 22a
; NO_WANT stops the matching of a want-true message by
; a true condition.  
(defn no_want (mess1 mess2)
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
(defn build_actions (rul confidence)
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
; the strength of the rule.  &lt;&lt;not used&gt;&gt;
 
(defn conclusion_confidence (rul)
   (times (get rul 'strength)
          (apply 'min (get rul 'condn_confidences))
   )
)
;********************************************************************* 24
;  PROJECT_TRUTH_VALUE returns a projected truth value.
 
(defn project_truth_value (val)
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
 
(defn change_activation ()
;d  (my_print '&quot;DEBUG change_activation just_activated &quot; just_activated
;d       '&quot; activated last time &quot; activated_last_time
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
(defn activ_ordinates (concept)
   (prog (ordinates first_ord result)
      (setq ordinates (append (get concept 'superordinates)
                              (get concept 'subordinates)
                      )
      )
      (setq result nil)
      
     
      loop
      (cond ( (null ordinates)
              (cond ( result
                      (my_print '&quot;Activating &quot;
                                (cond ((only_one result) '&quot;concept &quot;) 
                                      (t '&quot;concepts &quot;)
                                )
                                result
                                '&quot; by hierarchical spread from &quot;
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
(defn only_one (lst)
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
 
(defn set_activations (strucs fraction)
   (cond ( (null strucs) nil)
         (t (set_activation (car strucs) fraction)
            (set_activations (cdr strucs) fraction)
         )
   )
)
(defn set_activation (struc fraction)
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
(defn retrieve_messages ()
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
; &lt;&lt;break this code up&gt;&gt;
 
(defn execute_actions (rule_list)
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
                 (my_print '&quot;Activating concept &quot; new_concepts 
                           '&quot; by firing rule &quot;   rul		    
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
(defn defective_action (rul)
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
(defn is_existential (vbl)
   (atom_begins vbl #\l)
)
; *************************************************************  30
; RECORD_ACTIVATION stores with each concept the set of concepts
; that were directly responsible for its activation, i.e.
; the concepts in the conditions of the rule whose firing led
; to the activation of the concept.
(defn record_activation (rul actions)
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
; the form c -&gt; a and instantiating a would accomplish a goal or
; sub-goal, then c is added as a subgoal.
;
(defn set_sub_goals ()
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
(defn update_sub_goals (diff_g)
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
(defn sub_goal_find (rul)
; (my_print '&quot;subgoal finding on &quot; rul);   !
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
(defn build_sub_goals (condns actn rul)
   (declare (special actn) (special rul))
   (mapcar '(lambda (condn)
             ; (my_print '&quot;building subgoals from condition:  &quot; condn)  ; !!!!
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
                               (my_print '&quot;Activating concept &quot; (car condn)
                                         '&quot; by sub-goaling on &quot; rul
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
 
(defn classify (evidence object)
   (m_print '&quot;---------------------------------------------&quot;)
   (my_print '&quot;classifying &quot; object)
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
(defn update_mess (mess)
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
; &lt;confidence of old message&gt; + [(1 - &lt;conf. of old mess.&gt;) * &lt;conf. of new&gt;]
;  add:  handle contradictions and adjust confidence downwards.
;
(defn replace_mess (mess store_place)
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
(defn store_actions (actn)
 
;   if effector, start projection:    &lt;&lt;add:  handle move&gt;&gt;
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
(defn store_problem (prob_name)
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
(defn conc_from_prob (prob)
   (concepts_from (union (get prob 'start)
                         (get prob 'goals) 
                  )
   )
)
; ****************************************************************
; KEY_CONCEPTS_FROM ignores &quot;generic&quot; concepts that are less
; informative because they are so universal, e.g. spatial concepts.
(defn key_concepts_from (prob)
   (exclude generic_concepts (conc_from_prob prob))
)
; ****************************************************************
; GET_PROJECTED_RULES returns the rules used for a particular projection
; in a problem.  Like projecting_rules, this is awkward, and should not
; depend on car active_problems.
(defn get_projected_rules (projn)
   (get (car active_problems) projn)
)
; PUT_SOLUTION has the same flaw.
(defn put_solution (struc)
   (put struc 'old_solutions
              (cons (car active_problems) 
                    (get (car active_problems) 'old_solutions)
              )
   )
                   
)
 ;***************************************************************************
; UNSTORE simply deletes a stored message.
; &lt;&lt;Not used&gt;&gt;.
(defn unstore (mess store_place)
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
(defn store_expln (hypoth explanandum)
    
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
; hypotheses of the form Fa, or rules, of the form (x)(Fx-&gt;Gx).  
; Uses global variables:  competitors, evidence, best_exp, tie_flag.
(defn best_explanation? (hypoth)
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
           (my_print '&quot;The best explanation is: &quot; best_exp )
           (cond ( (equal (get best_exp 'data_type) 'hypothesis)
                   (my_print '&quot;                   &quot;(get best_exp 'message))
                 )
           )
           (my_print best_exp '&quot; explains: &quot; 
                     (remove_duplicates (get best_exp 'explains))
           )
           (my_print '&quot;Competing hypotheses: &quot;  competitors)
           (my_print '&quot;Co-hypotheses: &quot; (get best_exp 'co-hypotheses))
           (my_print '&quot;Total evidence: &quot; evidence)
           (cond ( tie_flag
                   (my_print '&quot;Tied hypotheses: &quot; tie_flag)
                 )
           )
         )
   )
   ; increase confidence/strength of best_exp, and decrease others.
   (adjust_conf best_exp competitors)
)
; ***********
(defn get_co-hyp (hyp)
    (get hyp 'co-hypotheses)
)
; ********************************************************************
; FIND_COMPETITORS finds all the competitors of a hypothesis. 
; A competitor is,
; at first approximation, a hypothesis that explains something that
; the original does.  The relation is transitive: if T1 explains
; E1 which is explained by T2 which explains E2 which is explained by
; T3, T1 and T3 should be competitors.  This function gets the entire set.
(defn find_competitors (hyp)
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
(defn explananda_of_list (lst)
   (remove_duplicates (union_map 'get_explananda lst))
)
(defn get_explananda (hyp)
   (get hyp 'explains)
)
(defn get_explainers (explanandum)
   (get explanandum 'explainers)
)
; ************************************************************
; BEST_EXP_OF picks the best explanation out of a set of competitors.
(defn best_exp_of (lst)
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
(defn better_expln (hyp1 hyp2)
   (or (better_expln_qual hyp1 hyp2)
       (better_expln_quant hyp1 hyp2)
   )
)
; ********************************************************
; BETTER_EXPLN_QUAL qualitatively determines the best explanation,
; using subset relations rather than metrics, resulting in more ties.
(defn better_expln_qual (hyp1 hyp2)
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
(defn note_tie (hyp1 hyp2)
   (setq tie_flag (cons (list hyp1 hyp2) tie_flag))
   hyp1  ; return hyp1 to keep comparison going.
)
(defn is_tie (result)
   (equal result 'tie)
)
; ***********************************************
; MORE_CONSILIENT determines whether a hypothesis explains more facts,
; or more consilient facts, than its competitors.
(defn more_consilient (hyp1 hyp2)
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
(defn simpler (hyp1 hyp2)
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
(defn simplicity (hyp)
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
(defn most_important (hyp1 hyp2)
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
(defn get_importance (atm) 
   (get atm 'importance)
)
; ********************************************************************
; COMPUTE_IMPORTANCES ensures that each of the explananda has an
; attached importance, taken from strength or activation.
(defn compute_importances (hyp)
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
(defn imp_rule (rul)
    (put rul 'importance (get rul 'strength))
)
(defn imp_fact (fact)        ; activation of concept fact belongs to
    (put fact 'importance 
              (get (get_predicate (get fact 'message))
                   'activation
              )
    )
)
(defn imp_default (x)
   (put_if_needed x 'importance 1)
)
;  add only if no value is already there:
(defn put_if_needed (atm place value)
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
(defn better_expln_quant (hyp1 hyp2)
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
(defn compute_expln (hyp)
   (times (simplicity hyp) (consilience_imp hyp))
)
   
; ***********************************************************
; CONSILIENCE_IMP measures not only the amount of facts 
; explained, but also how important they are.
(defn consilience_imp (hyp)
   (put hyp 'consilience_imp
       (quotient (total_importance (get hyp 'explains))
                 (total_importance evidence)
       )
   )
)
; ******************************************
; TOTAL_IMPORTANCE 
(defn total_importance (lst_of_explananda)
   (apply 'add (mapcar 'get_importance lst_of_explananda))
)
; *****************************************
; ADJUST_CONF increase the confidence of the best explanation and decreases
; that of the ones it beat.  Global:  hyp_msg
; &lt;&lt;ADD:  more principled adjustments, and update message list and instnaces.
(defn adjust_conf (best_hyp others)
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
(defn up_conf (num)
    (my_max 1 (add num .2))
)
(defn down_conf (hyp)     ; global:  msg
    (setq msg (get hyp 'message))
    (put hyp 'message
         (list (car msg) (second msg) (third msg) 
               .1
               (fifth msg)
         )
    )
)