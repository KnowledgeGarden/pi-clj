(ns pi-clj.concepts
  (:gen-class))

;  PURPOSE:     Concept formation, both from rules and by combination

; ********************************************************
;       Bottom-up concept formation 
;  *******************************************************
; RULES_WITH_SAME_CONDN finds all pairs of rules that have the
; same 2 or more conditions; returns a list of pairs.
(defn rules_with_same_condn (rule_list)
   (prog (rules rul rest_of_rules result)
      (binding rules rule_list)
      (binding result nil)
;     for each rule, check against rest of rules:
      loop1
      (cond ( (null rules) (return result) ))
      (binding rul (car rules))
      (binding rest_of_rules (cdr rules))
;        check against each remaining rule:
         loop2
         (cond  ( (null rest_of_rules)
                  (binding rules (cdr rules))
                  (go loop1)
                )
         )
;        see if 2 rules have same conditions:
         (cond ( (and (greaterp (length (get rul 'conditions)) 2)
                      (equal (get rul 'conditions)
                             (get (car rest_of_rules) 'conditions )
                      )
                 )
                 (binding result (cons (list rul (car rest_of_rules))
                                    result
                              )
                 )
               )
         )
         (binding rest_of_rules (cdr rest_of_rules))
         (go loop2)
   )
)
; **************************************************************
; FORM_CONCEPT_FROM_RULES produces a new concept from 2 rules with
; the same conditions, attaching to the new concept a new set of rules.
; note:  limited to forming unary concepts.
(defn form_concept_from_rules (list_of_two_rules)
 (prog (start_concs new_conc rule_1 rule_2)
    (binding rule_1 (car list_of_two_rules))
    (binding rule_2 (second list_of_two_rules))
;   create the new concept:
    (binding start_concs (concepts_from (get rule_1 'conditions) ))
    (binding new_conc (make_name start_concs) )
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
   (binding active_concepts (cons new_conc active_concepts))
;  make rules relating old and new concepts:
;  1.  old -&gt; new
   (make_rule_long new_conc
                   (get rule_1 'conditions)
                   (list (list new_conc '($x) 'true 'deduce) )
                   '???
                   'default
                   .2        ; arbitrary weak strength
   )
;  2.  new -&gt; old
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
(defn combine (concept1 concept2)
   (let (newconc new_concept_made)  
        (cond ( (and (name_not_in concept1 concept2)
                     (conflicting (get concept1 'rules)
                                  (get concept2 'rules)
                     )
                 )   
                 ; form new concept if originals conflict
                (binding newconc (concat concept1 '_ concept2))
                (binding new_concept_made
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
                      (my_print  '&quot;Conceptual combination producing: &quot; newconc)
                      (binding active_concepts (cons newconc active_concepts)) 
                      (build_all_rules newconc concept1 concept2)   ; add rules
                     )
               )
             )
          )
   new_concept_made  ; return name of concept if one was made
   )
)   
; ADD:  make rules for superordinates when this is appropriate.  E.g. 
;       sound_wave -&gt; wave.  Note this shouldn't apply to apartment_dog.
; This depends on kind of reconciliation required. 
 
;  ***********************************************************
; CONFLICTING checks to see if two concepts have any rules which
; would generate conflicting expectations.  e.g.  feminist and bank
; teller conflict, but bank teller and short do not.
; &lt;&lt;This should be more complicated:  conflict should require not
; only having rules in the same slot, but also a check for 
; conflicting values.  E.g. reflects and propagates can both
; be in a motion slot without conflict.  Need semantic 
; inconsistency.&gt;&gt; 
(defn conflicting (rules1 rules2)
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
             (list '&quot;Conflict: &quot; (car rules1) )
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
;(not (atom_includes name1 #\_ ))
          ;(not (atom_includes name2 #\_ ))
(defn name_not_in (name1 name2)
    (and  
          (not (atom_includes name1))
          (not (atom_includes name2))
          (null (member (concat name2 '_ name1) all_concepts))
    )
)
 
; ************************************************************
;  MAKE_MESSAGES creates messages.
(defn make_messages (newconc args)
   (prog (insts result)
      (binding insts args)
      (binding result nil)
      loop
      (cond ( (null insts) (return result)))
      (binding result 
            (cons (list newconc (list (car insts)) 'true .5)
                  result
            )
      )
      (binding insts (cdr insts))
      (go loop)
   )
)
;  ***********************************************************
 
;  BUILD_ALL_RULES (newconcept concept1 concept2) creates rules for
;  newconcept using the rules from the other two concepts.
 
(defn build_all_rules (newconcept concept1 concept2)
   (prog (c1_rules)
         (binding c1_rules (get concept1 'rules))
         loop
         (cond ((null c1_rules) (return '&quot;done combining.&quot;) ))
         (build_one_rule newconcept
                          (car c1_rules)
                          (get concept2 'rules)
         )
         (binding c1_rules (cdr c1_rules))
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
 
(defn build_one_rule (newconcept rule rulelist)
   (prog (c2_rules)
         (binding c2_rules rulelist)
         loop
         (cond ( (null c2_rules)
                 (return '&quot;no slot conflicts&quot;)
               )
          )
          (cond ( (equal (get rule 'slot)
                         (get (car c2_rules) 'slot)
                  )
                  (reconcile newconcept rule (car c2_rules))
                  (return '&quot;slot conflicts reconciled&quot;)
                )
          )
          (binding c2_rules (cdr c2_rules))
          (go loop)
   )
)
 
;  ************************************************************
 
;  assorted junk:
 
(defn pred_super (rule)
   (car (get (get_pred_r rule) 'superordinates))
)
 
(defn get_pred_r (rule)
   (car (car (get rule 'conditions)))
)
 
;
(defn isactual (rule1)
     (equal 'actual (get rule1 'status))
)
(defn isdefault (rule1)
      (equal 'default (get rule1 'status))
)
;  ************************************************************
;  RECONCILE produces a new rule from two conflicting ones.
;  global variables:  invar_r1, invar_r2, winner
(defn reconcile (newconcept rule1 rule2)
    (binding invar_r1 (invar (pred_super  rule1 )
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
            (binding winner rule1)
          )
          ( (and (isactual rule2)
                 (isdefault rule1)
            )
            (binding winner rule2)
          )
    
   ; pick most invariable
          ( (greaterp invar_r1 invar_r2)        
            (binding winner rule1)
          )
          ( (lessp invar_r1 invar_r2)
            (binding winner rule2)
          )
   ; decide on basis of property of common instance
          ( (binding winner (instance_decides (get_pred_r rule1)
                                           (get_pred_r rule2)
                                           rule1
                                           rule2
                         )
            )
            winner
          )
   ; default:  go with strongest rule - cruder measure of variability
          ( (greaterp (get rule1 'strength) (get rule2 'strength))
            (binding winner rule1)
          )
          (t (binding winner rule2) )
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
(defn invar (kind1 kind2)
   (prog (range varieties subkinds count)
         (cond ( (or (null kind1) (null kind2))  ; no kinds
                 (return 1)                     ; high default value
               )
         )
         (binding  range 0
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
         (binding count (countrules (car subkinds) kind2))
         (cond ( (greaterp count 0)
                 (binding range (add1 range))
               )
         )
         (binding varieties (add varieties count))
         (binding subkinds (cdr subkinds))
         (go loop)
   )
)
;  ************************************************************
 
;  COUNTRULES counts the number of rules that a concept has with a
;  a given slotname.  thus if parrots have two rules concerning color
;  countrules returns 2.
 
(defn countrules (concept slotname)
   (prog (rulelist result)
         (binding rulelist  (get concept 'rules)
               result 0
         )
         loop
         (cond ( (null rulelist) (return result)))
         (cond ( (equal (get (car rulelist) 'slot) slotname )
                 (binding result (add1 result))
               )
         )
         (binding rulelist (cdr rulelist))
         (go loop)
    )
)
;  ************************************************************
;  INSTANCE_DECIDES attempts reconciliation on the basis of what
;  instances two concepts have incommon.  If C1 and C2 have a
;  common instance with a property predicted by rule 1, then 
;  rule 1 is the winner.
(defn instance_decides (conc1 conc2 rule1 rule2)
   (prog (common_inst first_inst)
      (binding examples (common_inst conc1 conc2))
      loop
      (cond ( (null examples ) (return nil)))
      (binding first_inst (car examples))
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
      (binding examples (cdr examples))
      (go loop)
   )
)
; ********************************************************
; COMMON_INST returns the names of instances common to two concepts.
; Cf. getinstances, common, and common1 in gen.l.
; This works only for unary predicates.
(defn common_inst (conc1 conc2)
   (intersect (instances_from2 conc1)  ;cf gen.l
              (instances_from2 conc2)
   )
)
; 
(defn instances_from2 (conc)
   (mapcar 'first_arg (get conc 'instances))
)
;
(defn first_arg (mess) 
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
(defn full_combine (conc1 conc2 mode)
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
(defn intersect_combine (conc1 conc2)
   (let (new_conc)
        (binding new_conc (combine conc1 conc2)) ; structural combination
	(if new_conc (explain_combine new_conc conc1 conc2))
   )
)
; ****************************************************************
; EXPLAIN_COMBINE adds features to a combined concept based on what it
; takes to explain how, given one feature, the other is possible.
(defn explain_combine (combined_conc conc1 conc2)
   (let (start_conc explain_conc hypotheses)
        ; select the more salient concept as what is to be explained.
        (if (more_salient conc1 conc2)
            (and (binding explain_conc conc1)
                 (binding start_conc conc2)
            )
            ; else
            (and (binding explain_conc conc2)
                 (binding start_conc conc1)
            )
        )
        ; do an explanation:
        (binding hypotheses (chain_explain start_conc explain_conc))
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
(defn more_salient (conc1 conc2)
   (&gt; (get conc1 'activation) (get conc2 'activation))
)
; ****************************************************************
; CHAIN_EXPLAIN is like explain, except that when abduction forms
; a new hypothesis, the hypothesis is added to the list of goals to
; be explained, until a hypothesis is reached that corresponds to
; where the explanation was intended to begin.
; global variables:  chain_explain_flag, conc_to_explain_with
; Returns a list of hypotheses formed during the chaining.
; Should quit when conc1 is involved in a hypothesis.
(defn chain_explain (conc1 conc2)
   (let (old_hypoths)
        (binding chain_explain_flag t)
        (binding conc_to_explain_with conc1)
        (binding old_hypoths (get 'all_hypothesis 'members))
        (explain 'fact
                 (list (make_condition conc1))
                 (list (make_condition conc2))
        )
        ; turn off constants:
        (binding chain_explain_flag nil)
        (binding conc_to_explain_with nil)
        (binding stop_problem nil)
        ; return new hypotheses
        (set-difference (get 'all_hypothesis 'members)
                        old_hypoths
        ) ; returned
   )
)
; ****************************************************************
; ADD_HYP_RULES turns hypotheses H into rules C -&gt; H attached to
; concept C.  Hypotheses must have been part of the explanatory chain
; from the starting concept to the goal concept.
(defn add_hyp_rules (conc hypoths start_conc explain_conc)
   (my_print '&quot;Adding to &quot; conc '&quot; using &quot; hypoths)
   (prog (hyps hyp chain_of_hyps)
      (binding hyps hypoths)
      (binding chain_of_hyps (trace_expln_chain 
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
      (binding hyp (car hyps))
      (if (part_of_expln hyp chain_of_hyps)
          (make_rule conc conc 
                    (car (get hyp 'message))
                    ; slot determined by kind:
                    (car (get (car (get hyp 'message)) 'superordinates))
                    'default
                    .1
          )
      )
      (binding hyps (cdr hyps))
      (go loop)
   )
)
; ****************************************************************
; TRACE_EXPLN_CHAIN lists those hypotheses that played a direct role in
; a chain of explanations. Does depth-first search.  Returns whole path.
; Note:  will not get second path which might exist.
(defn trace_expln_chain (start_hyp explanandum)
   (prog (queue expansion)
      (binding queue (list (list start_hyp)))
      loop
      (cond ( (null queue) (return nil))
            ( (equal explanandum (caar queue))
              (return (reverse (car queue)))
            )
      )
      (binding expansion (expand_expln_chain (car queue)))
      (binding queue (cdr queue))
      (binding queue (append expansion queue))
      (go loop)
   )
)
; ***************************************************************
; EXPAND_EXPLN_CHAIN adds new possible paths.
(defn expand_expln_chain (hyp_path)
   (mapcar #'(lambda (hyp)
                (cons hyp hyp_path)
             )
           (get (car hyp_path) 'explains)
   )
)
; ***************************************************************
; FIND_MESS_NAME finds the name of a message having the given concept
; as predicate.  
(defn find_mess_name (conc mess_list)
   (prog (messages answer)
      (binding messages (mapcar #'(lambda (mess)
                                  (get mess 'message)
                               )
                               mess_list
                      )
      )
      (binding answer nil)
      loop
      (cond ( (null messages)
              (if (&gt; (length answer) 1)
                  (my_print '&quot;WARNING:  find_mess_name finds more than one hypothesis: &quot; answer)
              )
              (return (if (null answer) nil
                          (fifth (car answer))
                      )
              )
            )
      )
      (if (equal (caar messages) conc)
          (binding answer (cons (car messages) answer))
      )
      (binding messages (cdr messages))
      (go loop)
   )
)
      
; ******************************************************
; PART_OF_EXPLN determines if a hypothesis played a role in an
; explanation chain, either as a step or as a co-hypothesis.
(defn part_of_expln (hypoth chain_of_hypoth)
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