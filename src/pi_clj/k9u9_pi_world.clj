(ns pi-clj.k9u9_pi_world
  (:gen-class))

;  Purpose:     Creation of simulated environment.

;  WORLD is an N X N grid, with messages stored at each
;  entry corresponding to what would be observed at that
;  point in the grid.
;  Global variables:  X_COORD:  x coordinate.
;                     Y_COORD:  y coordinate.
;  Possible directions are NORTH, SOUTH, EAST, WEST,
;  with movement changing the values of the coordinates.
;
(SETQ WORLD_DEBUG T)
 
;********************************************************
(PROGN
;********************************************************
; MAKE_WORLD (N) sets up an N X N grid and establishes an
; initial location in the middle.
;
(defn MAKE_WORLD (SIZE)
   (DEFINE (WORLD ARRAY (SIZE SIZE) ))   ; make grid.
   (SETQ  WORLD_MADE T)                 ; flag
   (SETQ X_COORD (IDIVIDE SIZE 2))
   (SETQ Y_COORD (IDIVIDE SIZE 2))
   (SETQ WORLD_SIZE SIZE)
   (MY_PRINT '&quot;World made of size &quot; SIZE)
)
;*********************************************************
;  OBSERVE adds to the list of active messages those messages
;  available through observation at a particular place in the
;  world.
(defn OBSERVE ()
   (COND ( WORLD_MADE
           (SETQ ACTIVE_MESSAGES
                 (UNION ACTIVE_MESSAGES
                        (WORLD X_COORD Y_COORD)
                 )
           )
         )
    )
)
;**********************************************************
; MOVE_SYSTEM takes the information from an effector MOVE
; and relocates the system in the world appropriately, moving
; the appropriate number of steps in a given direction.
(defn MOVE_SYSTEM (DIRECTION STEPS)
   (COND ( (EQUAL DIRECTION 'NORTH)
           (SETQ X_COORD (ADD X_COORD STEPS))
         )
         ( (EQUAL DIRECTION 'SOUTH)
           (SETQ X_COORD (SUB X_COORD STEPS))
         )
         ( (EQUAL DIRECTION 'EAST)
           (SETQ Y_COORD (ADD Y_COORD STEPS))
         )
         ( (EQUAL DIRECTION 'WEST)
           (SETQ Y_COORD (SUB Y_COORD STEPS))
         )
    )
   ;  Keep the system from falling off the grid:
   (COND ( (LESS X_COORD 1) (SETQ X_COORD 1) )
         ( (GREATER X_COORD WORLD_SIZE) (SETQ X_COORD WORLD_SIZE) )
   )
   (COND ( (LESS Y_COORD 1) (SETQ Y_COORD 1) )
         ( (GREATER Y_COORD WORLD_SIZE) (SETQ Y_COORD WORLD_SIZE) )
   )
   (COND ( WORLD_DEBUG (DESCRIBE_WORLD) ))
)
;***************************************************************
;  ADJUST keeps the system from falling off the grid, by ensuring
;  the x and y coordinates never get too big or small.
;
(defn ADJUST (COORD)
   (COND ( (LESS COORD 0) (SETQ COORD 0) )
         ( (GREATER COORD WORLD_SIZE) (SETQ COORD WORLD_SIZE) )
   )
)
;******************************************************************
(defn DESCRIBE_WORLD ()
  (MY_PRINT '&quot;X coordinate: &quot; X_COORD '&quot; Y coordinate: &quot; Y_COORD
            '&quot; Messages: &quot; (WORLD X_COORD Y_COORD)
  )
)
;******************************************************************
(PRINT '&quot;PI.WORLD loaded.&quot;)
                                  ;  end PROGN
;*****************************************************; FILE:         wts.l
; PURPOSE:      discovery and evaluation of wave theory of sound
; PROGRAMMER:   Paul Thagard
; CREATED:      9-30-86
; UPDATED:      12-1-86
(run 15)
(clear_all)
(setq print_to_file nil)
(setq analogy_flag nil)
(my_print '&quot;***********************************************&quot;)
(my_print '&quot;Running PI with input data/wts.l.&quot;)
(my_print '&quot;Problem:  How to explain properties of sound?&quot;)
(defn lf () (load &quot;prob_spread.l&quot;))
(defn ld () (load &quot;wts.l&quot;))
(setq trace_data t)
(setq trig_analog nil)
; **************************************************************
; Concepts:
(make_concept_s '(sensation physical_phenomenon voice music whistle bang
                  entertainment singing device jump is_heard goes_through_air
                  near hears echoes is_obstructed spread_plane swell
                  has_crest vibrate movement 
                  spread_spherically spread_plane thing plays instrument
                  pass_through lyre_music flute_music  lyre change
                 )
)
(make_concept 'sound 
              '(sensation physical_phenomenon)
              '(voice music whistle bang)
              nil nil 0
)
(make_concept 'propagate '(motion) nil nil nil 0)
(make_concept 'reflect '(motion_back) nil nil nil 0)
(make_concept 'motion '(change)
                      '(propagate reflect pass_through) nil nil 0
)
(make_concept 'pass_through '(motion) nil nil nil 0)
(make_concept 'music '(sound entertainment) '(instrumental_music singing)
              nil nil 0
)
(make_concept 'instrumental_music '(music) '(lyre_music flute_music)
              '( (instrumental_music (obj_a) true))
              nil 0
)
(make_concept 'instrument '(device) '(stringed_instrument) 
              nil nil 0
)
(make_concept 'stringed_instrument '(instrument) '(lyre)
              '( (stringed_instrument (obj_b) true))
              nil 0
)
(make_concept 'move_up_down '(movement) '(wave jump) 
              nil nil 0
)
(make_concept 'wave '(movement) '(water_wave hand_wave) nil nil 0)	      
(make_concept 'motion_back '(motion) '(reflect bounce) nil nil 0)
(make_concept 'bounce '(motion_back) nil '((bounce (obj_c) true))
              nil 0
)

; **************************************************************
; Rules about sound:
; R0:  Anything heard is a sound.
(make_rule 'is_heard  'is_heard 'sound 'result 'actual 1)
; R1:  sounds are transmitted by air.
(make_rule 'sound 'sound 'goes_through_air 'transmission 'default .8)
; R2:  sounds are heard by persons near them.
(make_rule_long 'sound 
                '( (sound ($x) true) (person ($y) true) (near ($x $y) true))
                '( (hears ($y $x) true))
                'effect
                'default
                .7
)
; R3:  obstructed sounds echo.
(make_rule_long 'sound
                '( (sound ($x) true ) (is_obstructed ($x) true) )
                '( (echoes ($x) true))
                'obstruction_result
                'default
                .4
)
; R4:  sounds spread spherically.
(make_rule 'sound 'sound 'spread_spherically 'spread_shape 'default .9)
; *******************************************************
; Rules about waves:
; R5:  Waves spread in a plane.
(make_rule 'wave 'wave 'spread_plane 'spread_shape 'default .7)
; R6:  Waves are swells.
(make_rule 'wave 'wave 'swell 'motion_shape  'default .6)
; R7:  Waves propagate.
(make_rule 'wave  'wave 'propagate 'motion 'default .8)
; R8:  Waves have crests.
(make_rule 'wave 'has_crest 'shape 'motion 'default .8)
; R9:  Waves reflect.
(make_rule_long 'wave
                '((wave ($x) true) )
                '((reflect ($x) true))
                'obstruction_effect
                'default
                .6
)
; R10:  Waves pass through each other.
(make_rule 'wave 'wave 'pass_through 'motion 'default .9)
; ***********************************************************
; R11:  Balls propagate.
(make_rule 'ball 'ball 'propagate 'motion 'default .9)
; R12:  Balls reflect.
(make_rule 'ball 'ball 'reflect 'motion 'default .8)

; ***********************************************************
;  Miscellaneous rules.
; R13:  Music is pleasant.
(make_rule 'music 'music 'pleasant 'affect 'default .5)
; R14:  Instruments are delicate.
(make_rule 'instrument 'instrument 'delicate 'quality 'default .6)
  
; ***********************************************************
; Rules for associating from sounds to waves:
; R15:  Instrumental music is played by instruments.
(make_rule_long 'instrumental_music
                '( (instrumental_music ($x) true))
                '( (instrument (%y) true) (plays (%y $x) true))
                'method
                'actual
                1
)
                 
; R16:  Stringed instruments vibrate.
(make_rule 'stringed_instrument 'stringed_instrument 'vibrate 'movement 
           'default .7
)
; R17:  To vibrate is to move up and down.
(make_rule 'vibrate 'vibrate 'move_up_down 'move_shape 'default .8)


; ***********************************************************
; Rule to associate reflect -&gt; ball.
; R18:  Bouncing is  done by balls.
(make_rule_long 'bounce
                '((bounce ($x) true))
                '((ball ($x) true) )
                'performer
                'default
                .6
)
                        
; ***********************************************************
(setq trace_data t)
; ***********************************************************
(make_problem 'sound_reflect
              '( (sound ($x) true))
              '( (propagate ($x) true)
                 (reflect ($x) true)
                 (pass_through ($x) true)
               )
              'explanandum
)
(put 'sound_reflect 'explan_status 'explanation)
(setq activated_last_time nil)
(solve_problem 'sound_reflect)