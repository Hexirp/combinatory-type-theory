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

(** [I] を定義します。 *)

Definition
  I@{i | }
    : forall A : Type@{i}, A -> A
    := fun A : Type@{i} => fun x : A => x
.

(** [K] を定義します。 *)

Definition
  K@{i | }
    : forall A : Type@{i}, forall B : Type@{i}, B -> A -> B
    := fun A : Type@{i} => fun B : Type@{i} => fun y : B => fun x : A => y
.

(** [B0] を定義します。 *)

Definition
  B0@{i | }
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

(** [B1] を定義します。 *)

Definition
  B1@{i | }
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

(** [C0] を定義します。 *)

Definition
  C0@{i | }
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

(** [C1] を定義します。 *)

Definition
  C1@{i | }
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

(** [C2] を定義します。 *)

Definition
  C2@{i | }
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

(** [C3] を定義します。 *)

Definition
  C3@{i | }
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

(** [S0] を定義します。 *)

Definition
  S0@{i | }
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

(** [S1] を定義します。 *)

Definition
  S1@{i | }
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

(** [S2] を定義します。 *)

Definition
  S2@{i | }
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

(** [S3] を定義します。 *)

Definition
  S3@{i | }
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

(** [S4] を定義します。 *)

Definition
  S4@{i | }
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

(** [S6] を定義します。 *)

Definition
  S6@{i | }
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

(** [S7] を定義します。 *)

Definition
  S7@{i | }
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

(** [T] を定義します。 *)

Definition
  T@{i si | i < si}
    : Type@{si}
    := Type@{i}
.

(** [P0] を定義します。 *)

Definition
  P0@{i | }
    : Type@{i} -> Type@{i} -> Type@{i}
    := fun A : Type@{i} => fun B : Type@{i} => A -> B
.

(** [P1] を定義します。 *)

Definition
  P1@{i | }
    : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
    := fun A : Type@{i} => fun B : A -> Type@{i} => forall x : A, B x
.

Section Assertion.

Universe i si.

Constraint i < si.

Check I@{i}.

Check
  I@{i}
    :
      P1@{si}
        T@{i si}
        (
          fun A : T@{i si} =>
            P0@{si}
              A
              A
        )
.

Check
  I@{i}
    :
      P1@{si}
        T@{i si}
          (
            S0@{si}
              T@{i si}
              T@{i si}
              T@{i si}
              (
                B0@{si}
                  T@{i si}
                  T@{i si}
                  (
                    P0@{si}
                    T@{i si}
                    T@{i si}
                  )
                  P0@{i}
                  (
                    I@{si}
                      T@{i si}
                  )
              )
              (
                I@{si}
                  T@{i si}
              )
          )
.

End Assertion.
