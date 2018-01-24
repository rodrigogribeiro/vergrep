Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".
Set Implicit Arguments.

From QuickChick Require Import QuickChick.

Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Require Import
        Ascii
        List
        ListDec
        String
        Tests.Generators.GenString
        Utils.Functions.ListUtils
        Utils.Functions.StringUtils.

Definition parts_non_empty (s : string) :=
  forallb (@non_empty ascii) (parts (string_to_list s)).

QuickChick (forAll gen_string parts_non_empty).

Definition parts_correct (s : string) :=
  forallb (fun xs => if string_dec (list_to_string (concat xs)) s then true
                  else false)
          (parts (string_to_list s)).

QuickChick (forAll gen_string parts_correct).