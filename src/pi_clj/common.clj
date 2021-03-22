(ns pi-clj.common
  (:gen-class))

; PURPOSE:     Running PI in common lisp.

; For conversion from Franz to Common:
(defn greaterp (num1 num2) (&gt; num1 num2))
(defn lessp (num1 num2) (&lt; num1 num2))
(defn plist (atm) (symbol-plist atm))
(defn quotient (num1 num2) (/ num1 num2))
 
(defn times (&amp;rest arguments) (apply '* arguments))
(defn diff (num1 num2) (- num1 num2))
(defn add (&amp;rest arguments) (apply '+ arguments))
(defn add1 (num) (+ 1 num))
(defn memberlist (lst1 lst2) (member lst1  lst2 :test 'equal)) ; otherwise uses eq
(defn subsetlist (lst1 lst2) (subsetp lst1 lst2 :test 'equal))
 
; *********************************************************
; For conversion from old Michigan lisp to Common:
(defn put (atm prop val) (setf (get atm prop) val))
(defn divide (num1 num2) (/ num1 num2))
 
(defn sub (num1 num2) (- num1 num2))
(defn intersect (lst1 lst2) (intersection lst1 lst2))
; *********************************************************
; For general conversion:
(defn my_max (num1 num2) (max num1 num2))
(defn subset (l1 l2) (subsetp l1 l2))
(defn remove_duplicates (lst) (remove-duplicates lst :test #'equal ))
; MY_PRINT prints out any number of arguments.
(defvar where_to_print *standard-output*)   ; optional output stream
(defn my_print (&amp;rest arguments)
   (prog (args)
      (binding args arguments)
      loop
      (cond ( (null args) (terpri where_to_print) (return t)))
      (princ (car args) where_to_print)
      (binding args (cdr args))
      (go loop)
   )
)


; ***********************************************************
; For atom making (from Marie):
; CONCAT ; THIS DEPENDS ON STRING-APPEND, WHICH WAS ONLY
; IN SUN COMMON LISP.   REPLACE WITH PATCH AT TOP OF THIS PAGE.
;(defn concat (&amp;rest concat-things)
;  &quot;Take any number of strings, atoms or numbers, smash them together,
;   (after making them all into strings) and return a symbol of the result.&quot;
;   (read-from-string (apply 'string-append 
;		           (mapcar 'coerce-string concat-things)))
;)
(defn coerce-string (thing)
  &quot;Make a thing (number, symbol, string) into a string.&quot;
       (cond ((numberp thing)
              (prin1-to-string thing))
             ((symbolp thing)
              (symbol-name thing))
             ((stringp thing)
              thing))
)
;; BEGIN newsym functions (similar to gensym)
(defvar *NEWSYM-PREFIX* 'c)

(defn newsym (symb)
  &quot;Given a symbol, get it's counter and create a new symbol consisting
   of the symbol concat'ed with its number.  If symbol is nil, use 
   the current value of *NEWSYM-PREFIX*&quot;
   (cond ((symbolp symb)
          (if (null symb) (binding symb *NEWSYM-PREFIX*))
          (let (count)
               (if (null (get symb '*newsym-counter*))
                   (setf (get symb '*newsym-counter*) 0))
               (setf (get symb '*newsym-counter*)
                     (add1 (binding count (get symb '*newsym-counter*))))
               (concat symb count)))
         (t (println "Error: non-symbol arg to newsym")
            (println symb)))
)
; **********************************************************
; ATOM_BEGINS checks to see whether an atom begins with a
; given character.
(defn atom_begins (atm char)
   (and (atom atm)  (eq (aref (coerce-string atm) 0) char))
)

; ATOM_INCLUDES checks to see whether an atom includes a given
; character.
; *************
; @see https://stackoverflow.com/questions/7491360/how-do-you-return-from-a-function-early-in-clojure
; CLOJURE DOES NOT HAVE "RETURN"
(defn atom_includes (atm char)
   (do (str index)
      (binding str (symbol-name atm))
      (binding index 0)
      (go 
         (loop
            (if (&gt; (+ 1 index) (length str)) (return nil))
            (if (equal (aref str index) char) (return t))
            (binding index (+ 1 index))
         ))
   )
)
         
; ************************************************************


; ************************************************************
; For convenience:
(defn q () (quit))
(defn exit () (quit))
(defn unix (str) (run-unix-program str))
(defn lv+ () (binding *load-verbose* t))
(defn lv- () (binding *load-verbose* nil))

; ***************************************************************
; For more informative printing:
(binding *print-level* 20)
(binding *debug-print-level* 20)
(binding *print-length* 100)
(binding *debug-print-length* 100)
