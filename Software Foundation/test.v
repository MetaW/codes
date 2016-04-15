Module wll.
  Inductive hehe: Type :=
   | aaa : hehe
   | bbb : hehe.

  Check aaa.

Definition nex (n:nat):nat :=
  S n.

Compute nex 12.

End wll.

Compute wll.nex 12.

Check wll.aaa.