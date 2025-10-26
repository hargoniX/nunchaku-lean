import Nunchaku
import Test.Eval.Sound
import Test.Eval.Perf

-- TODO: Figure out where Subtype.elim_20 did not get killed
#eval_nunchaku_sound_decl Array.size_uset

-- TODO: handle Std.Associative
#eval_nunchaku_sound_decl List.foldr_assoc

-- TODO: handle False.rec
-- TODO: handle exists being used to build a dependent and
-- TODO: handle casts

-- TODO: Figure out where Sum.rec is coming from
#eval_nunchaku_sound_decl Sum.map_inl
