(ns pi-clj.trig
  (:gen-class))

; PURPOSE:          Triggering conditions for inference in PI

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
;              (&lt;explanandum&gt; &lt;explaining rule&gt; &lt;condition to abduce&gt;)
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
(defn trigger ()
   (cond (trace_prob (my_print '&quot;Triggering inductions ...&quot;)))
;  identify concepts with common instances:
   (setq common_concepts (get_common_concepts))
 
;  trigger instance-based generalization and conceptual combination:
   (cond ( common_concepts (mapcar 'trig_gen_comb common_concepts)))
 
;  trigger generalization involving relations:
;  &lt;&lt;this needs to be more selective, counting instances.&gt;&gt;
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
;      concerning something &quot;unusual&quot; about the same object.
 
; trigger abduction
   (cond ( (get (car active_problems) 'explan_status) ; expln. context
            ;abduction to fact:
            (trig_abduce)
            ;  abduction to rule 
            (trig_abd_gen)   ; see explain.l
         )
    )
;  trigger formation of new concepts from active rules with the
;  same set of at least 2 conditions, i.e. from a&amp;b&amp;c -&gt; d and a&amp;b&amp;c -&gt; d
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
 
(defn trig_gen_comb (triple)
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
 
(defn trig_cond_gen (quadruple)
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
(defn more_active_than (struc thresh)
   (&gt; (get struc 'activation) thresh)
)
; **********************************************************
;  GET_COMMON_CONCEPTS searches through the message list for instances
;  of concepts in common, e.g. for concepts a and b which both have object
;  o as instances.   Algorithm:  for each message, see if any of the
;  rest of the messages have the same instances.  Returns a list of
;  triples, (concept1 concept2 vbl?).
;
(defn get_common_concepts ()
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
                     ; ignore if both messages are projected:  &lt;kluge for c.c.&gt;
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
; a &amp; b -&gt; c,  a &amp; d -&gt; c, so a -&gt; c.  takes candidates got from
; common_action, having the form (rule1 rule2 action_to_gen),
; and returns the same list with condn_to_gen added to the end.
;
(defn get_common_rules (candidates)
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
(defn common_action (rules)
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
(defn condn_gen (rule1 rule2 action_to_gen condn_to_gen)
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
           (my_print '&quot;condition-based generalization from &quot;
                     (list rule1 rule2) '&quot; to &quot; concpt '&quot; --&gt; &quot; actn_concpt
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