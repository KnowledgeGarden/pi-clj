(ns pi-clj.misc
    (:require [pi-clj.common :as c])
   (:gen-class))

;  PURPOSE:     Miscellaneous utility functions for PI
;*********************************************************************** 22
;  TRUTH_COMPATIBLE checks that two messages have compatible
;  truth values
(c/>put 'true  'truthkind  't)
(c/>put 'proj_true 'truthkind 't)
(c/>put 'want_true 'truthkind 't)
(c/>put 'false 'truthkind 'f)
(pc/>put 'proj_false 'truthkind 'f)
(c/>put 'want_false 'truthkind 'f)
 
(defn truth_compatible (mess1 mess2)
   (c/>put 'true 'truthkind 't)
   (equal (get (third mess1) 'truthkind)
          (get (third mess2) 'truthkind)
   )
)
; ********************************************************************* 
;  MAXIMUM gives the greatest of a list of values
(defn maximum (numlist)
   (apply 'max numlist)
)
;
; ********************************************************************* 
; MAX1 returns no higher than 1:
(defn max1 (num)
   (if (&gt; num 1) 1 num)
)
; *******************************************************
; EXCLUDE (list1 list2) returns a list consisting of list2 with
; all the elements of list1 removed.
(defn  exclude (list1 list2) (set-difference list2 list1))
;**********************************************************
; UNION_LIST takes any number of arguments and returns the
; union of all of them.
(defn union_list (&amp;rest arguments)           ; takes any number of arguments
    (remove-duplicates (apply 'append arguments))
)
; ********************************************************
; UNION_MAP takes the union of all members of a list of lists,
; where the list of lists arises from mapcarring a function.
; e.g. union_map  'cdr  '( (a b) '( 1 2 a)) = (b 2 a)
(defn union_map (fn lst)
   (apply 'union_list (mapcar fn lst))
)
;**********************************************************
; INTERSECTION_LIST takes any number of arguments and returns 
; their intersection.
(defn intersection_list (&amp;rest arguments)
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
(defn apply_union (lst)
    (apply 'union_list lst)
)
;
(defn apply_intersection (lst)
    (apply 'intersection_list lst)
)
;**********************************************************
 
;**********************************************************
(defn not_equal (s1 s2)
   (not (equal s1 s2))
)
 
(defn not_member (el lst)
  (cond ( (memberlist el lst) nil )
        ( t t)
  )
)
; ATOMCAR  ; buggy
(defn atomcar (atm)
   (coerce (aref (symbol-name atm) 0) 'atom)
)
; ATOMCDR: modify for commonlisp.
(defn atomcdr (atm)
   (implode (cdr (explode atm)))
)
; 
   
; ***********************************************************
; REMOVE_LIST removes all members of list1 from list2
(defn remove_list (lst1 lst2)
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
 
(defn highest (list property)
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
(defn no_nils (lst)       ;  lst has no nil elements
   (cond ( (null lst) t)
         ( (null (car lst)) nil)
         (t (no_nils (cdr lst)))
   )
)
; *************************************************************
;  slow_print prints everything out on its own line
(defn slow_print (lst)
    (mapcar 'my_print lst)
)
; *************************************************************
; PRINT_PLIST_S prints out the plists of all members of a list
(defn print_plist_s (lst)
    (mapcar 'print_plist lst)
)
 
(defn pls (lst) (mapcar 'print_plist lst))
 
;***************************************************************
 
 
;  DUMP_ALL prints out the property lists of all rules and
;  concepts.
;
(defn dump_all ()
   (my_print '&quot;++++++++++++++++++++++++++++++++++++++++++++++++&quot;)
   (my_print '&quot;dumping entire system:&quot;)
   (my_print '&quot;all rules:&quot;)
   (mapcar 'print_plist
           all_rules
   )
   (my_print '&quot;all concepts:&quot;)
   (mapcar 'print_plist
           all_concepts
   )
   (dump_messages)
   (my_print '&quot;active problems:&quot;)
   (mapcar 'print_plist
           all_problems
   )
   
)
; ****************************************************************************
; DUMP_MESSAGES prints out all_hypotheses, etc.
(defn dump_messages ()
    (mapcar 'print_plist (union (get 'all_hypothesis 'members)
                                (get 'all_explanandum 'members)
                         )
    )
)
;******************************************************************************
 
;  DUMP_ACTIVE prints out the property lists of all active rules and
;  concepts.
;
(defn dump_active ()
   (my_print '&quot;dumping active system:&quot;)
   (my_print '&quot;active rules:&quot;)
   (mapcar '(lambda (rul)
              (my_print  rul (plist rul) )
            )
           active_rules
   )
   (my_print '&quot;active concepts:&quot;)
   (mapcar '(lambda (conct)
               (my_print  conct (plist conct) )
            )
           active_concepts
 
   )
   (my_print '&quot;active problems:&quot;)
   (mapcar '(lambda (prob)
               (my_print prob (plist prob) )
            )
           active_problems
 
   )
   (my_print '&quot;all rules: &quot; all_rules)
   (my_print '&quot;all concepts: &quot; all_concepts)
   (my_print '&quot;*************end dump*******************&quot;)
)
; **************************************************************************
; print_plist pretty-prints out a property list.
(defn print_plist (atm)
   (prog (lst)
       (my_print '&quot;   &quot;)
       (my_print '&quot;Property list of &quot;  atm)
       (setq lst (plist atm))
       loop
       (cond ( (null lst) (return t)))
       (my_print (car lst) '&quot;:  &quot; (cadr lst))
  
       (setq lst (cddr lst))
       (go loop)
   )
)
(defn pl (atm) (print_plist atm))
;*************************************************************************
; MAKE_NAME makes a name a_b_c_... out of a set of atoms.
(defn make_name (list_of_atoms)
   (apply 'concat list_of_atoms)
)
 
; **********************************************************
; NAME_MESSAGE adds a name to a message, indicating what type
; it is.  The message structure becomes:
; (predicate arguments truth-value confidence name)
; Appropriate names:  goal, explanandum, message, hypothesis.
; global variable:  newname
(defn name_message (mess type)
   (setq newname (newsym type))
   (setq typeclass (concat 'all_ type) )
   (c/>put newname 'data_type type)
   (c/>put newname 'importance 1)     ; default for goals and explananda
   (c/>put typeclass 'members (cons newname (get typeclass 'members)))
   (setf typeclass (cons newname typeclass)) ; won't work
   (c/>put newname 'message
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
(defn make_want (value)
   (cond ( (equal value 'true) 'want_true)
         ( (equal value 'false) 'want_false)
         ( t value)
   )
)
; **********************************************************
; NAME_MESS_LIST does a bunch of messages at once
(defn name_mess_list (mess_list type)
   (cond ( (null mess_list) nil)
         ( t (cons (name_message (car mess_list) type)
                   (name_mess_list (cdr mess_list) type)
             )
         )
   )
) 
;**********************************************************
; useful for mapcarring:
(defn get_solutions (concpt)
;s   (print concpt) 
;s   (print (get concpt 'old_solutions))
;s   (terpri)
   (get concpt 'old_solutions)
)
(defn get_rules (concpt)
   (get concpt 'rules)
)
(defn get_objects (concpt)
   (union_map 'get_argument 
              (get concpt 'instances)
   )
)
(defn get_activation (struc)
    (get struc 'activation)
)
; *******************************************************
; DISPLAY_VALS gives a set of values from plists of a set.
(defn display_vals (lst prop)
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
(defn mess_on (mess mess_lst sought_or_found)
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
(defn clear_all ()
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
(defn nillify (atm)
    (setq atm nil)
)
; CLEAR_PROPS
(defn clear_props (atm)
   (mapcar #'(lambda (prop)
               (c/>put atm prop nil)
            )
            (every_second (plist atm))
    )
)
; ****************************************************
; UN_REFRACT removes a record of previous matches so that
; rules can fire again.
(defn un_refract (rul)
    (c/>put rul 'old_matches nil)
)
; ****************************************************
; EVERY_SECOND gets the first, third, fifth, etc. members
; of a list.
(defn every_second (lst)
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
(defn project_mess (mess)
   (subst (project_truth_value (third mess)) (third mess) mess)
)
; *******************************************************
; For name manipulation:
; NEWATOM 
(defn newatom (stem)
   (prog1 (intern (string (gensym stem))))
)
; *******************************************************
 
; *******************************************************
; OBJ_FROM_PROB states all the objects used in a problem.
(defn obj_from_prob (prob)
   (union_map #'second (union (get prob 'start) (get prob 'goals)))
)
; ****************************************************************
; FIND_DUPLICATES names all the redundant members of a list.
(defn find_duplicates (list_of_atoms)
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
(defn conc_from_prob (prob)
   (remove-duplicates (concepts_from (union (get prob 'start)
                                            (get prob 'goals) 
                                      )
                      )
   )
)
;  ************************************************************************ 
;  CONCEPTS_FROM returns a list of all the concepts used in a list of
;  conditions, actions, or messages
(defn concepts_from (mess_list)
   (mapcar 'car mess_list)
)
;
;  ************************************************************************ 
; CONS_IF_NEW adds an element if it is not already there.
(defn cons_if_new (el lst)
   (if (member el lst) lst
       ; else
       (cons el lst)
   )
)
;  ************************************************************************ 
;  MIN_MAX returns a value between low and high.
(defn min_max (low high num) (min (max low num) high))
;  ************************************************************************ 
;  REMOVE_NIL_DUP removes nil and duplicate elements.
(defn remove_nil[A_dup (lst)
   (remove-duplicates (remove nil lst))
)
;  ************************************************************************ 
; MY_OPEN opens a file for outc/>put:
(defn my_open (string)
   (setq where_print_before where_to_print)
   (setq where_to_print     ;  see my_print in common.l
         (open string :direction :outc/>put :if-exists :append
                      :if-does-not-exist :create
         )
   )
)
; *********************************************************************
; MY_CLOSE closes an open outc/>put file and returns to standard outc/>put
(defn my_close (stream)
   (close stream)
   (setq where_to_print where_print_before)
)