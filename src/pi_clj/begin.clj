(ns pi-clj.analog
  (:gen-class))
;;  PURPOSE:       Central file for system PI (Processes of Induction)
;;                 Program written in Common Lisp, running on a Sun 3/75
;;                 under UNIX.
;;                 Includes functions for running system
;;                and functions for making
;;                the central  data structures of PI:  concepts,
;;                rules, objects, problems.

   (my_print &quot;Welcome to PI.  This program is copyright (c) 1988 Paul Thagard.&quot;)
   (my_print &quot;Permission is hereby granted for use for research purposes,&quot;)
   (my_print &quot;   but denied for commercial or military purposes.&quot;)
   (my_print &quot;It comes with no warranty.&quot;)
;**********************************************************
 
;  PI   files:         (add suffix &quot;.l&quot;)
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
;       data/cup        input data for cup &amp; paper problem
;       data/breed.l    analogical abduction
;       data/exist.l    existential abduction
;       data/fem-banl.l conceptual combination
;       data/fort.l     problem solving by analogy
;       data/gen_lon    data for generalization with relations
;       data/ray        data for ray problem - analogy
;       data/spec       input data for specialization
;       data/theor      data for theory evaluation
;       data/theor2     theory evaluation
;       data/wts1       data for propagation -&gt; wave theory of sound
;       data/wts2       data for reflection -&gt; wave theory of sound
;       data/wts3       data for propagation &amp; reflection -&gt; wave theory
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
 
(defn run_pi (trace_data? trace_prob? max_rules?  deact_conc?
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
         rel_motiv_flag          nil        ;      &quot;
         chain_explain_flag      nil        ; see concepts.l
         conc_to_explain_with    nil        ;      &quot;
	 
         ; constants:
         confidence_threshold   .5
         ; available variables:
         univ_vbls    '($x $y $z $u $v $w $d $e $f)  ; universal
         exist_vbls   '(%x %y %z %u %v %w %a %b %c %d %e %f %g %h)  ; existential
         all_exist_vbls '(%x %y %z %u %v %w %a %b %c %d %e %f %g %h) 
    	 vbl_list      (union univ_vbls exist_vbls  ) 
   )
   (setq debug nil)
   
   (my_print '&quot;PI initialized.&quot;)
)
;  to make life easy, just call run which sets defaults:
(defn run (steps)
   (run_pi 'true 'true 10  .1 .001 1 .2 steps)
)
;**********************************************************
 
;**********************************************************
;*    functions for creating data structures:             *
;**********************************************************
;  MAKE_PROBLEM constructs a problem with goals and starting conditions:
 
(defn make_problem (problem_name start_list goal_list type)
   (setq all_problems (cons problem_name all_problems))
   (put problem_name 'goals 
        (name_mess_list goal_list type)
   ) 
   (put problem_name 'data_type 'problem)
   (put problem_name 'start start_list)
   (put problem_name 'activation 0)
   (cond ( trace_data
           (my_print '&quot;Problem made:  &quot; problem_name)
         )
   )
)
 
;  ************************************************************
 
;  assorted junk:
 
(defn make_condition (pred)
    (list pred '($x) 'true )
)
(defn make_action (pred)
    (list pred '($x) 'true  'deduce)
)
 
; ************************************************************
; PROJECTS checks whether any of the actions of a rule are effectors
; that would start projections.
(defn projects (actions)
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
 
(defn make_rule (conct pred1 pred2 slo stat stren )
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
 
(defn make_rule_long (conct condns actns slo stat stren )
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
              (my_print '&quot;Rule made: &quot;  result)
              (my_print '&quot;  &quot;  (concepts_from condns) '&quot; -&gt; &quot; 
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
 
(defn redundant (condns actns  rule_list)
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
 
;  MAKE_CONCEPT constructs a concept named &quot;conct&quot; with lists of
;  superordinates, subordinates, instances, rules, and degree of activation.
 
 
(defn make_concept (conct superord subord inst ruls activn)
;  check for redundancy:
   (declare (special conct))
   (cond ( (member conct all_concepts)
           nil                     ; no concept made
         )
         ( t                       ; otherwise, make concept:
 
           (cond ( trace_data (my_print '&quot;Concept made: &quot; conct)))
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
(defn make_concept_s (lst)
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
(defn make_object (name lst)
   (cond ( (null name)
           (setq obj_name (newsym 'obj_))
           (intern obj_name)
         )
         (t (setq obj_name name))
   )
   (prog (l property)
         (setq l lst)
         loop
         (cond ( (null l)  (return '&quot;object made&quot;) ) )
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
(defn get_predicate (mess)
   (car mess)
)
 
(defn get_argument (mess)
   (second mess)
)
 
(defn get_truth (mess)
    (third mess)
)
 
(defn get_confidence (mess)
    (cond ( (fourth mess) (fourth mess) )
          ( t 1)       ; default confidence is 1)
    )
)
(defn get_effect_status (actn)
    (fourth actn)
)
(defn projn_from_mess (mess)
    (cond ( (listp (fifth mess)) (fifth mess))
          ( t (list (fifth mess)))
    )
)
; Note:  most messages have confidence in fourth place;
; actions in rules to be defined have effector status:
; effect or deduce.
