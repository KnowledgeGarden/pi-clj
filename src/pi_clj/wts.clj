(ns pi-clj.wts
  (:gen-class)
    (:require [pi-clj.misc :as wts])
    (:require [pi-clj.common :as common])

)

; PURPOSE:      discovery and evaluation of wave theory of sound
;;(run 15)
(clear_all)
(setq print_to_file nil)
(setq analogy_flag nil)
(my_print '"***********************************************")
(my_print '"Running PI with input data/wts.l.")
(my_print '"Problem:  How to explain properties of sound?")
(defn lf () (load "prob_spread.l"))
(defn ld () (load "wts.l"))
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
; Rule to associate reflect -> ball.
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