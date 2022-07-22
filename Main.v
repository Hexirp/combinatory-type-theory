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
  FI@{i | } (A : Type@{i})
    : A -> A
    := fun x : A => x
.

(** [FK] を定義します。 *)

Definition
  FK@{i | } (A : Type@{i}) (B : Type@{i})
    : B -> A -> B
    := fun (y : B) (x : A) => y
.

(** [FB] を定義します。 *)

Definition
  FB@{i | } (A : Type@{i}) (B : Type@{i}) (C : B -> Type@{i})
    : (forall y : B, C y) -> forall (y : A -> B) (x : A), C (y x)
    := fun (z : forall y : B, C y) (y : A -> B) (x : A) => z (y x)
.

(** [FB0] を定義します。 *)

Definition
  FB0@{i si | i < si} (A : Type@{i}) (B : Type@{i}) (C : Type@{i})
    : (B -> C) -> (A -> B) -> A -> C
    := FB@{i} A B (FK@{si} B Type@{i} C)
.

(** [FB1] を定義します。 *)

Definition
  FB1@{i | } (A : Type@{i}) (B : Type@{i}) (C : B -> Type@{i})
    : (forall y : B, C y) -> forall (y : A -> B) (x : A), C (y x)
    := FB@{i} A B C
.

(** [FC] を定義します。 *)

Definition
  FC@{i | } (A : Type@{i}) (B : Type@{i}) (C : A -> B -> Type@{i})
    : (forall (x : A) (y : B), C x y) -> forall (y : B) (x : A), C x y
    := fun (z : forall (x : A) (y : B), C x y) (y : B) (x : A) => z x y
.

(** [FC0] を定義します。 *)

Definition
  FC0@{i si | i < si} (A : Type@{i}) (B : Type@{i}) (C : Type@{i})
    : (A -> B -> C) -> B -> A -> C
    := FC@{i} A B (FK@{si} A (B -> Type@{i}) (FK@{si} B Type@{i} C))
.

(** [FC1] を定義します。 *)

Definition
  FC1@{i si | i < si} (A : Type@{i}) (B : Type@{i}) (C : B -> Type@{i})
    : (A -> forall y : B, C y) -> forall y : B, A -> C y
    := FC@{i} A B (FK@{si} A (B -> Type@{i}) C)
.

(** [FC2] を定義します。 *)

Definition
  FC2@{i si ssi | i < si, si < ssi} (A : Type@{i}) (B : Type@{i}) (C : A -> Type@{i})
    : (forall x : A, B -> C x) -> B -> forall x : A, C x
    := FC@{i} A B (FB0@{si ssi} A Type@{i} (B -> Type@{i}) (FK@{si} B Type@{i}) C)
.

(** [FC3] を定義します。 *)

Definition
  FC3@{i | } (A : Type@{i}) (B : Type@{i}) (C : A -> B -> Type@{i})
    : (forall (x : A) (y : B), C x y) -> forall (y : B) (x : A), C x y
    := FC@{i} A B C
.

(** [FS] を定義します。 *)

Definition
  FS@{i | } (A : Type@{i}) (B : A -> Type@{i}) (C : forall x : A, B x -> Type@{i})
    : (forall (x : A) (y : B x), C x y) -> forall (y : forall x : A, B x) (x : A), C x (y x)
    := fun (z : forall (x : A) (y : B x), C x y) (y : forall x : A, B x) (x : A) => z x (y x)
.

(** [FS0] を定義します。 *)

Definition
  FS0@{i si | i < si} (A : Type@{i}) (B : Type@{i}) (C : Type@{i})
    : (A -> B -> C) -> (A -> B) -> A -> C
    := FS@{i} A (FK@{si} A Type@{i} B) (FK@{si} A (B -> Type@{i}) (FK@{si} B Type@{i} C))
.

(** [FS1] を定義します。 *)

Definition
  FS1@{i si | i < si} (A : Type@{i}) (B : Type@{i}) (C : B -> Type@{i})
    : (A -> forall y : B, C y) -> forall (y : A -> B) (x : A), C (y x)
    := FS@{i} A (FK@{si} A Type@{i} B) (FK@{si} A (B -> Type@{i}) C)
.

(** [FS2] を定義します。 *)

Definition
  FS2@{i si ssi | i < si, si < ssi} (A : Type@{i}) (B : Type@{i}) (C : A -> Type@{i})
    : (forall x : A, B -> C x) -> (A -> B) -> forall x : A, C x
    := FS@{i} A (FK@{si} A Type@{i} B) (FB0@{si ssi} A Type@{i} (B -> Type@{i}) (FK@{si} B Type@{i}) C)
.

(** [FS3] を定義します。 *)

Definition
  FS3@{i si | i < si} (A : Type@{i}) (B : Type@{i}) (C : A -> B -> Type@{i})
    : (forall (x : A) (y : B), C x y) -> forall (y : A -> B) (x : A), C x (y x)
    := FS@{i} A (FK@{si} A Type@{i} B) C
.

(** [FS4] を定義します。 *)

Definition
  FS4@{i si | i < si} (A : Type@{i}) (B : A -> Type@{i}) (C : Type@{i})
    : (forall x : A, B x -> C) -> (forall x : A, B x) -> A -> C
    := FS@{i} A B (fun x : A => FK@{si} (B x) Type@{i} C)
.

(** [FS6] を定義します。 *)

Definition
  FS6@{i si | i < si} (A : Type@{i}) (B : A -> Type@{i}) (C : A -> Type@{i})
    : (forall x : A, B x -> C x) -> (forall x : A, B x) -> forall x : A, C x
    := FS@{i} A B (fun x : A => FK@{si} (B x) Type@{i} (C x))
.

(** [FS7] を定義します。 *)

Definition
  FS7@{i | } (A : Type@{i}) (B : A -> Type@{i}) (C : forall x : A, B x -> Type@{i})
    : (forall (x : A) (y : B x), C x y) -> forall (y : forall x : A, B x) (x : A), C x (y x)
    := FS@{i} A B C
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
    := fun (A : Type@{i}) (B : Type@{i}) => A -> B
.

(** [TP1] を定義します。 *)

Definition
  TP1@{i | }
    : forall A : Type@{i}, (A -> Type@{i}) -> Type@{i}
    := fun (A : Type@{i}) (B : A -> Type@{i}) => forall x : A, B x
.
