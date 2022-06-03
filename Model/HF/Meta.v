(** Coq coding by choukh, May 2022 **)

Require Export Utf8_core Setoid Morphisms.
Global Set Implicit Arguments.
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.
Global Hint Extern 4 => exact _ : core. (* 让auto策略可使用typeclass实例 *)

Declare Scope hf_scope.
Delimit Scope hf_scope with hf.
Open Scope hf_scope.

(* 存在量词式Σ类型记法 *)
Notation "'Σ' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
    format "'[' 'Σ'  '/ ' x .. y ,  '/ ' p ']'") : type_scope.

(** 配合HF强归纳, 提取Σ类型见证 **)
Class 可判定 (P : Prop) : Set := 判定 : {P} + {¬ P}.

Arguments 判定 P {可判定}.

Tactic Notation "判定" constr(P) "as" simple_intropattern(i) := 
  destruct (判定 P) as i.

Notation "'可识别' T" := (∀ x y : T, 可判定 (x = y)) (at level 70) : hf_scope.

Fact 相等可判定_对称 {T} (x y : T) : 可判定 (x = y) → 可判定 (y = x).
Proof. unfold 可判定. intuition. Qed.
