(ns pi-clj.ana_scheme
  (:gen-class))
;; PURPOSE:     analogical schema formation in PI

; ******************************************
; SCHEM_ALL is called by solve_problem when a problem solution has
; been achieved using an analogous concept solution.  
; old_anas is a list of triples: base target analogous_concepts.
(defn schem_all (prob_name old_anas)
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

(defn schematize (prob1 prob2 ana)
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
	   (my_print '&quot;Analogical schema produced: &quot; schema)
	 )
   )
 )
)
; **************************************************************
; STORE_SOLUTION associates concepts with schematic solutions.
(defn store_solution (prob concepts)
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
(defn abstract_list (mess_lst1 mess_lst2 ana)
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
(defn abstract_mess (mess1 mess2 ana)
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
(defn analogous (conc1 conc2 ana)
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
(defn related? (mess1 mess2)
   (cond ( (equal (car mess1) (car mess2)) (list (car mess1)))
         (t (or (abstract_conc (car mess1) (car mess2) )
	        (abstract_objs (second mess1) (second mess2))
            )
         )
   )
)   
; *************************************************************
; ABSTRACT_CONC finds an abstraction from two concepts based on their
; rules.  If A --&gt; C, and B --&gt; C, then C is an abstraction of both
; A and B.  E.g. animal is an abstraction of cats and dogs, because
; all cats and dogs are animals.  Obviously, there can be more than
; one abstraction.
; More thoroughly, we could do a search up the default 
; hierarchy, so that if A --&gt; D --&gt; C, and B --&gt; E --&gt; C, then C
; would be an abstraction.  This would be done implicitly by 
; abstract_objs, since rule firing would have led to the 
; conclusions that follow.
(defn abstract_conc (conc1 conc2)
    (intersect (possible_abstrns conc1)
	       (possible_abstrns conc2)
    )
)
; **************************************************************
; POSSIBLE_ABSTRNS looks through the rules attached to a concept C
; for simple ones of the form C --&gt; A, returning A as a possible
; abstraction.
(defn possible_abstrns (conc)
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
(defn abstract_objs (obj_lst1 obj_lst2)
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
(defn common_properties (obj1 obj2)
   (intersect (concepts_from (unary_preds (get obj1 'messages)))
              (concepts_from (unary_preds (get obj2 'messages)))
   )
)
; **************************************************************
; UNARY_PREDS returns a list of only 1-place predicates from a list
; of messages.
(defn unary_preds (mess_list)
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
(defn assign_vbls (arg_lst1 arg_lst2)
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
(defn de_project_val (val)
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
(defn schem_rules (pro1 pro2 ana schem)
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
(defn schem_rule (rul prob ana schem)
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
