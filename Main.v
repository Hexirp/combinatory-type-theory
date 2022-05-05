(** [ltac_plugin] を読み込みます。 *)

Declare ML Module "ltac_plugin".

(** [ssrmatching_plugin] を読み込みます。 *)

Declare ML Module "ssrmatching_plugin".

(** [ssreflect_plugin] を読み込みます。 *)

Declare ML Module "ssreflect_plugin".

(** 対話的な証明を行う時のモードを [Classic] にセットします。 *)

Global Set Default Proof Mode "Classic".

(** ゴールのセレクタのデフォルトを [all] にします。 *)

Global Set Default Goal Selector "all".

(** [Elimination Schemes] をオフにします。 *)

Global Unset Elimination Schemes.

(** [Universe Polymorphism] をオンにします。 *)

Global Set Universe Polymorphism.

(** [Polymorphic Inductive Cumulativity] をオンにします。 *)

Global Set Polymorphic Inductive Cumulativity.

(** 宇宙階層を表示するようにします。 *)

Global Set Printing Universes.

(** [forall (_ : x), y] の糖衣構文として [x -> y] を定義します。 *)

Notation
  "x -> y" := (forall (_ : x), y)
    (at level 99, right associativity, y at level 200)
.

(** [FI] を定義します。 *)

Definition
  FI@{i | }
    : forall A : Type@{i}, A -> A
    := fun A : Type@{i} => fun x : A => x
.

(** [FK] を定義します。 *)

Definition
  FK@{i | }
    : forall A : Type@{i}, forall B : Type@{i}, B -> A -> B
    := fun A : Type@{i} => fun B : Type@{i} => fun y : B => fun x : A => y
.

(** [FB0] を定義します。 *)

Definition
  FB0@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : Type@{i},
            (B -> C) -> (A -> B) -> A -> C
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : Type@{i} =>
            fun z : B -> C =>
              fun y : A -> B =>
                fun x : A =>
                  z (y x)
.

(** [FB1] を定義します。 *)

Definition
  FB1@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : B -> Type@{i},
            (forall y : B, C y)
              ->
                forall y : A -> B,
                  forall x : A,
                    C (y x)
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : B -> Type@{i} =>
            fun z : forall y : B, C y =>
              fun y : A -> B =>
                fun x : A =>
                  z (y x)
.

(** [FC0] を定義します。 *)

Definition
  FC0@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : Type@{i},
            (A -> B -> C) -> B -> A -> C
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : Type@{i} =>
            fun z : A -> B -> C =>
              fun y : B =>
                fun x : A =>
                  z x y
.

(** [FC1] を定義します。 *)

Definition
  FC1@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : B -> Type@{i},
            (A -> forall y : B, C y)
              ->
                forall y : B,
                  A -> C y
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : B -> Type@{i} =>
            fun z : A -> forall y : B, C y =>
              fun y : B =>
                fun x : A =>
                  z x y
.

(** [FC2] を定義します。 *)

Definition
  FC2@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : A -> Type@{i},
            (forall x : A, B -> C x)
              ->
                B
                  ->
                    forall x : A,
                      C x
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : A -> Type@{i} =>
            fun z : forall x : A, B -> C x =>
              fun y : B =>
                fun x : A =>
                  z x y
.

(** [FC3] を定義します。 *)

Definition
  FC3@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : A -> B -> Type@{i},
            (forall x : A, forall y : B, C x y)
              ->
                forall y : B,
                  forall x : A,
                    C x y
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : A -> B -> Type@{i} =>
            fun z : forall x : A, forall y : B, C x y =>
              fun y : B =>
                fun x : A =>
                  z x y
.

(** [FS0] を定義します。 *)

Definition
  FS0@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : Type@{i},
            (A -> B -> C) -> (A -> B) -> A -> C
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : Type@{i} =>
            fun z : A -> B -> C =>
              fun y : A -> B =>
                fun x : A =>
                  z x (y x)
.

(** [FS1] を定義します。 *)

Definition
  FS1@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : B -> Type@{i},
            (A -> forall y : B, C y)
              ->
                forall y : A -> B,
                  forall x : A,
                    C (y x)
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : B -> Type@{i} =>
            fun z : A -> forall y : B, C y =>
              fun y : A -> B =>
                fun x : A =>
                  z x (y x)
.

(** [FS2] を定義します。 *)

Definition
  FS2@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : A -> Type@{i},
            (forall x : A, B -> C x)
              ->
                (A -> B)
                  ->
                    forall x : A,
                      C x
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : A -> Type@{i} =>
            fun z : forall x : A, B -> C x =>
              fun y : A -> B =>
                fun x : A =>
                  z x (y x)
.

(** [FS3] を定義します。 *)

Definition
  FS3@{i | }
    :
      forall A : Type@{i},
        forall B : Type@{i},
          forall C : A -> B -> Type@{i},
            (forall x : A, forall y : B, C x y)
              ->
                forall y : A -> B,
                  forall x : A,
                    C x (y x)
    :=
      fun A : Type@{i} =>
        fun B : Type@{i} =>
          fun C : A -> B -> Type@{i} =>
            fun z : forall x : A, forall y : B, C x y =>
              fun y : A -> B =>
                fun x : A =>
                  z x (y x)
.

(** [FS4] を定義します。 *)

Definition
  FS4@{i | }
    :
      forall A : Type@{i},
        forall B : A -> Type@{i},
          forall C : Type@{i},
            (forall x : A, B x -> C) -> (forall x : A, B x) -> A -> C
    :=
      fun A : Type@{i} =>
        fun B : A -> Type@{i} =>
          fun C : Type@{i} =>
            fun z : forall x : A, B x -> C =>
              fun y : forall x : A, B x =>
                fun x : A =>
                  z x (y x)
.

(** [FS6] を定義します。 *)

Definition
  FS6@{i | }
    :
      forall A : Type@{i},
        forall B : A -> Type@{i},
          forall C : A -> Type@{i},
            (forall x : A, B x -> C x)
              ->
                (forall x : A, B x)
                  ->
                    forall x : A,
                      C x
    :=
      fun A : Type@{i} =>
        fun B : A -> Type@{i} =>
          fun C : A -> Type@{i} =>
            fun z : forall x : A, B x -> C x =>
              fun y : forall x : A, B x =>
                fun x : A =>
                  z x (y x)
.

(** [FS7] を定義します。 *)

Definition
  FS7@{i | }
    :
      forall A : Type@{i},
        forall B : A -> Type@{i},
          forall C : forall x : A, B x -> Type@{i},
            (forall x : A, forall y : B x, C x y)
              ->
                forall y : forall x : A, B x,
                  forall x : A,
                    C x (y x)
    :=
      fun A : Type@{i} =>
        fun B : A -> Type@{i} =>
          fun C : forall x : A, B x -> Type@{i} =>
            fun z : forall x : A, forall y : B x, C x y =>
              fun y : forall x : A, B x =>
                fun x : A =>
                  z x (y x)
.

(** [TU] を定義します。 *)

Definition
  TU@{i si | i < si}
    : Type@{si}
    := Type@{i}
.

(** [TP0] を定義します。 *)

Definition
  TP0@{i | }
    : Type@{i} -> Type@{i} -> Type@{i}
    := fun A : Type@{i} => fun B : Type@{i} => A -> B
.

(** [TP1] を定義します。 *)

Definition
  TP1@{i | }
    : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
    := fun A : Type@{i} => fun B : A -> Type@{i} => forall x : A, B x
.

Section Assertion.

Universe i si.

Constraint i < si.

Check FI@{i}.

Check
  FI@{i}
    :
      TP1@{si}
        TU@{i si}
        (
          fun A : TU@{i si} =>
            TP0@{i}
              A
              A
        )
.

Check
  FI@{i}
    :
      TP1@{si}
        TU@{i si}
        (
          FS0@{si}
            TU@{i si}
            TU@{i si}
            TU@{i si}
            (
              FB0@{si}
                TU@{i si}
                TU@{i si}
                (
                  TP0@{si}
                    TU@{i si}
                    TU@{i si}
                )
                TP0@{i}
                (
                  FI@{si}
                    TU@{i si}
                )
            )
            (
              FI@{si}
                TU@{i si}
            )
        )
.

Check FK@{i}.

Check
  FK@{i}
    :
      TP1@{si}
        TU@{i si}
        (
          fun A : TU@{i si} =>
            TP1@{si}
              TU@{i si}
              (
                fun B : TU@{i si} =>
                  TP0@{i}
                    B
                    (
                      TP0@{i}
                        A
                        B
                    )
              )
        )
.

Check
  FK@{i}
    :
      TP1@{si}
        TU@{i si}
        (
          fun A : TU@{i si} =>
            TP1@{si}
              TU@{i si}
              (
                FS0@{si}
                  TU@{i si}
                  TU@{i si}
                  TU@{i si}
                  (
                    FB0@{si}
                      TU@{i si}
                      TU@{i si}
                      (
                        TP0@{si}
                          TU@{i si}
                          TU@{i si}
                      )
                      TP0@{i}
                      (
                        FI@{si}
                          TU@{i si}
                      )
                  )
                  (
                    FB0@{si}
                      TU@{i si}
                      TU@{i si}
                      TU@{i si}
                      (
                        TP0@{i}
                          A
                      )
                      (
                        FI@{si}
                          TU@{i si}
                      )
                  )
              )
        )
.

End Assertion.
