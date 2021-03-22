(ns pi-clj.cause
  (:gen-class))

; PURPOSE:      causal reasoning
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
(defn make_event (temporal spatial descriptions)
   (let ((evnt (newsym 'event_)))
        (put evnt 'time temporal)
        (put evnt 'space spatial)
        (put evnt 'descriptions descriptions)
        (setq all_events (cons evnt all_events))
        (my_print '&quot;Event made:&quot;)
        (print_plist evnt)
        evnt
   )
)
; ******************************************************
; data abstraction for events:
(defn event_time (evnt)
   (get evnt 'time)
)
(defn event_space (evnt)
   (get evnt 'space)
)
(defn event_start (evnt)
   (car (event_time evnt))
)
(defn event_end (evnt)
   (cadr (event_time evnt))
)
(defn x_coords (evnt)
   (car (event_space evnt))
)
(defn y_coords (evnt)
   (second (event_space evnt))
)
(defn z_coords (evnt)
   (third (event_space evnt))
)
 
(defn event_descriptions (evnt)
   (get evnt 'descriptions)
)
(defn event_causes (evnt)
   (get evnt 'causes)
)
(defn event_effects (evnt)
   (get evnt 'effects)
)

    
; *******************************************************
; SIMULTANEOUS determines that two events take place over exactly the 
; same time.
(defn simultaneous (ev1 ev2)
   (and (equal (event_start ev1) (event_start ev2))
        (equal (event_end ev1) (event_end ev2))
   )
)
; *******************************************************
; BEFORE returns true if e1 happened before e2.
(defn before (e1 e2)
   (and (&lt; (event_start e1) (event_start e2))
        (&lt;= (event_end e1) (event_end e2))
   )
)
; ********************************************************
; AFTER
(defn after (e1 e2)
   (and (&gt; (event_start e1) (event_start e2))
        (&gt;= (event_end e1) (event_end e2))
   )
)
; ********************************************************
; CONTIGUOUS:  two events are spacially contiguous if all their
; spatial coordinates intersect.
   
(defn contiguous (ev1 ev2)
   (and (overlap (x_coords ev1) (x_coords ev2))
        (overlap (y_coords ev1) (y_coords ev2))
        (overlap (z_coords ev1) (z_coords ev2))
   )
)
; ********************************************************
; OVERLAP is true if two sets of coordinates intersect.
(defn overlap (coords1 coords2)
   (or (num_between (car coords1) coords2)
       (num_between (cadr coords1) coords2)
   )
)
; *************************************************************
; NUM_BETWEEN:  a is between (b c) if b &lt;= a &lt;=c.
(defn num_between (num nums)
   (and (&lt;= (car nums) num)
        (&lt;= num (cadr nums))
   )
)
; **************************************************************
; HEUR1_BEFORE is a causal heuristic that says that if one event
; is before another, it might be the cause.
(defn heur1_before (ev1 ev2)
   (cond ( (before ev1 ev2)
           (my_print ev1 '&quot; is before &quot; ev2 '&quot;.  Value: &quot; heur1_val)
           heur1_val
         )
         (t 0)
   )
)
; ********************************************************
; HEUR2_CONTIG says that contiguous events are more likely to be causally
; related.
(defn heur2_contig (ev1 ev2)
   (cond ( (contiguous ev1 ev2)
           (my_print ev1 '&quot; is contiguous with&quot; ev2 
                         '&quot;.  Value: &quot; heur2_val)          
           heur2_val
         )
         (t 0)
   )
)
; ******************************************************
; HEUR3_COMMON checks for a common cause.
(defn heur3_common (ev1 ev2)
   (cond ( (common_cause ev1 ev2) 
           (my_print &quot;Common cause found for &quot; ev1 '&quot; and &quot; ev2)
	   0
         ) 
         (t heur3_val)
   )
)
; ******************************************************
; COMMON_CAUSE checks to see if two events have a common cause.
; A more thorough version of this would do a search to set up
; the event causes.
(defn common_cause (ev1 ev2)
   (intersect (event_causes ev1) (event_causes ev2))
)
; ******************************************************
; HEUR4_CHAIN looks to see if there is a chain of causal rules leading 
; from descriptions of one event to descriptions of another.
; chain_limit is a constant of how deep to search, i.e. how many
; inferences to allow in a chain.
(setq chain_limit 5)
(defn heur4_chain (ev1 ev2)
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
                (my_print '&quot;Causal chain found between &quot; ev1 '&quot; and &quot; ev2)
                (my_print '&quot;Descriptions satisfied:  &quot;  goals_satisfied)
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
(defn cause? (ev1 ev2)
   (let (cause_val)
        (setq cause_val
              (times (heur1_before ev1 ev2)
                     (heur2_contig ev1 ev2)
                     (heur3_common ev1 ev2)
                     (heur4_chain  ev1 ev2)
              )
        )
        (my_print '&quot;Causal value: &quot; cause_val)
        (cond ( (&gt; cause_val cause_threshold) 
                (my_print ev1 '&quot; causes &quot; ev2)
                t
              )
              (t nil)
        )
   )
)