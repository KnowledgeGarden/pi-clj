(ns pi-clj.gen
  (:gen-class))

; PURPOSE:       Generalization and specialization
; **********************************************
; somewhat arbitrary constants:
(setq gen_threshold .5)        ; minimum strength for generalization
(setq max_instances 20)        ; maximum number of instances
; *********************************************
 
; GENERALIZE constructs synchronic rules by generalization,
; setting the strength of the rule on the basis of number
; of instances and variability.
;
(defn generalize (triple)
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
            (my_print class '&quot; --&gt; &quot; property
                      '&quot; generalized from &quot;
                      common_instances
                      '&quot; instances.&quot;
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
;  of property. (2 ways: typicality &gt; 0 vs. 0, or just not listed).
;   failures to check should trigger refutation or specialization.
;   confirmations should add to strength of rule.
; see below, near end of file.
; *********************************************
;
; GETINSTANCES returns a list of the instances of a class.  Note
; that it gets subordinates' instances as well..
 
(defn getinstances (class)
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
(defn instances_from (concpt)
   (union_map 'get_argument
              (get concpt 'instances)
   )
) 
; *******************************************************
;
; GETSUBKINDS lists the subkinds of a class:
 
(defn getsubkinds (class)
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
 
(defn common (class1 class2)
  (intersection (getinstances class1)
                (getinstances class2)) )
 
; this is implausible &lt;???&gt;
; since you may not have accessible e.g. all blue things.
; perhaps classes like bird have locatable instances, but not properties.
; hence the function common should function to find the common instances
; of a class and a property by checking each instance of the class
; to see if it has the property:
 
 
(defn common1 (class property)
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
 
(defn is? (thing property)
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
; example: (loves ($x $y)) (nice ($x))   -&gt;  (loves ($y $x)).
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
(defn gen_long (list_of_two_lists)
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
 
(defn clear_vbls (inst)
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
(defn fix_vbls (instance)
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
 
(defn fix_action (instance)
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
(defn check (prop1 prop2)
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
(defn get_instances (prop truth_val)
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
; should be formed.  e.g. from a--&gt;b to a&amp;c--&gt;b.
;
(defn trig_spec (prop1 prop2 inst)
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
; FIND_RULE looks for the existence of a rule a-&gt;b.
; it checks the list of rules attached to the concept a.
; returns name of the found rule. limited to simple rule.
(defn find_rule (prop1 prop2)
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
; if the generalization a--&gt;b fails with the counterinstance c,
; then we look for something unusual about c.  these can either be
; a property of c that all a's lack, or a property of all a's that
; c lacks.  in the former case, we want to specialize a&amp;~p--&gt;b.
; in the latter, a&amp;p--&gt;b.   limited to unary predicates.
; global variable: weird: the unusual condition.
;
(defn spec (prop1 prop2 inst old_rul)
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
(defn unusual (prop1 prop2 inst)
    (or (prop_not_inst prop1 prop2 inst)
        (inst_not_prop prop1 inst)
    )
 
)
; **********************************************************
; PROP_NOT_INST finds a property p3 of all instances of a property p1
; not shared by the given instance i.
; global variable: poss_props  weird_pred
;
(defn prop_not_inst (prop1 prop2 inst)
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
(defn inst_not_prop (prop inst)
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
(defn get_all_properties (instances)
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
;   conditions &amp; goal --&gt; actions
; this can be thought of both as a generalization about the goal,
; or as a specialization of the rule.
;
(defn gen_goal (rule_list)
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
; &lt;&lt;Fix to make vbl_lst local variable.  Cf. fix_vbls.&gt;&gt;
(defn make_wants (mess_list gen?)
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