(** * The spare frame: recursion through [Acc], and its extraction

    Outside [make demo], straight in Rocq ([make frame]), in the mode of
    [Print nat_rect]: no kernel of the lecture is needed.

    - [Acc] and [Acc_rect]: a proof of accessibility is a tree whose
      children are the proofs for the smaller elements; [Acc_rect] is
      structural recursion on that tree, the [fix] the guard accepts.
    - [g] of lecture 7, [g 0 = 0] and [g (succ k) = g (pred k)], refused
      there and by the guard here ([pred k] is no subterm of [succ k]),
      defined through [Acc_rect] on [<]: the recursive call goes to
      [pred k] with the proof [pred k < succ k].
    - Its equations hold, whatever the proof of accessibility; [lt_wf]
      being transparent, it also computes in Rocq, through the proofs.
    - Its extraction: the proof of accessibility is gone — [Acc lt n] is
      a proposition, erased as the propositions of the lecture are — and
      the recursion stays: [Acc_rect] becomes [let rec g_acc], and the
      proof of [pred k < succ k] the erased argument [__]. *)

From Stdlib Require Import Arith Wf_nat Lia Extraction.

Print Acc.
Print Acc_rect.
Print nat_rect.

Lemma pred_lt_succ : forall k, pred k < S k.
Proof. intros k. lia. Qed.

(** One step of [g]: [rec] is [g] on the smaller elements. *)
Definition g_step (n : nat) : (forall m, m < n -> nat) -> nat :=
  match n return (forall m, m < n -> nat) -> nat with
  | 0 => fun _ => 0
  | S k => fun rec => rec (pred k) (pred_lt_succ k)
  end.

Definition g_acc : forall n, Acc lt n -> nat :=
  Acc_rect (fun _ => nat) (fun n _ rec => g_step n rec).

Definition g (n : nat) : nat := g_acc n (lt_wf n).

(** The result does not depend on the proof of accessibility. *)
Lemma g_acc_irrelevant : forall n (a b : Acc lt n), g_acc n a = g_acc n b.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction lt_wf).
  intros [h] [h']. destruct n as [|k]; [reflexivity | ]. cbn. apply IH, pred_lt_succ.
Qed.

Lemma g_acc_succ : forall k h, g_acc (S k) (Acc_intro _ h) = g_acc (pred k) (h (pred k) (pred_lt_succ k)).
Proof. reflexivity. Qed.

Lemma g_zero : g 0 = 0.
Proof. unfold g. destruct (lt_wf 0). reflexivity. Qed.

Lemma g_succ : forall k, g (S k) = g (pred k).
Proof.
  intros k. unfold g. destruct (lt_wf (S k)) as [h]. rewrite g_acc_succ. apply g_acc_irrelevant.
Qed.

(** [lt_wf] is transparent: [g] also computes in Rocq, through the proofs. *)
Eval vm_compute in List.map g (0 :: 1 :: 2 :: 5 :: 10 :: nil).

Recursive Extraction g.
