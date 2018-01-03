Require Import
        Ascii
        String
        Bool
        List
        Substring.SubstringAntimirov
        Substring.SubstringBrzozowski.

From Coq Require Extraction.

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.


Extract Inductive unit    => "()" [ "()" ].
Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sum     => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive list    => "[]" ["[]" "(:)"].
Extract Inductive prod    => "(,)" ["(,)"].
Extract Inductive sigT    => "(,)" ["(,)"].
Extract Inductive option  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inlined Constant andb      => "(Prelude.&&)".
Extract Inlined Constant app       => "(Prelude.++)".
Extract Inlined Constant bool_dec  => "(Prelude.==)".
Extract Inlined Constant map       => "(Prelude.map)".
Extract Inlined Constant fst       => "Prelude.fst".
Extract Inlined Constant length    => "Data.List.length".
Extract Inlined Constant minus     => "(Prelude.-)".
Extract Inlined Constant mult      => "(Prelude.*)".
Extract Inlined Constant negb      => "Prelude.not".
Extract Inlined Constant orb       => "(Prelude.||)".
Extract Inlined Constant plus      => "(Prelude.+)".
Extract Inlined Constant ascii_dec => "(Prelude.==)".
Extract Inlined Constant string_dec => "(Prelude.==)".
Extract Inlined Constant proj1_sig => "".
Extract Inlined Constant projT1    => "Prelude.fst".
Extract Inlined Constant snd       => "Prelude.snd".
Extract Inlined Constant existsb   => "Prelude.any".
Extraction Implicit eq_rect [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec [ x y ].
Extraction Implicit eq_rec_r [ x y ].

Extract Inlined Constant eq_rect => "".
Extract Inlined Constant eq_rect_r => "".
Extract Inlined Constant eq_rec => "".
Extract Inlined Constant eq_rec_r => "".
Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "(Prelude.succ)"]
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive string => "Prelude.String" ["[]" "(:)"].
Extract Inductive ascii => "Prelude.Char" [""].

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].

Extract Inlined Constant Arith.Plus.tail_plus => "(Prelude.+)".

Cd "./build/src".

Separate Extraction brzozowski_substring.
Separate Extraction antimirov_substring.