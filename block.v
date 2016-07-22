(*Principled tactical blocking of parts of a goal.

Useful for directing a tactic's impact on specific parts of that goal while
avoiding impact on others.  For example, blocking the conclusion at a point
will make it impervious to intros past that point.  Blocking equality hyps
will prevent subst from using them (unless the hyp is a local def and is
mentioned explicitly as a subst arg).  Blocking existing hyps prior to some
tactic that introduces new hyps will make it easy to distinguish the new hyps
from the old ones.

Blocks can nest.

Blocking will not impact the proof term or Extraction.

However, note that vm_compute and native_compute (as of 8.5pl1) can circumvent
Opaqueness, so do not use these tactics in a blocked goal.

*)

Local Definition block {T}(a:T) := a.
Extraction Inline block.
Opaque block.
Local Definition ublock {T}(a:T) := a.

Ltac block_term_in_hyp term H :=
  change term with (block term) in (type of H).
Ltac unblock_term_in_hyp term H :=
  change (block term) with term in (type of H).
Ltac block_term_in_conc term :=
  change term with (block term).
Ltac unblock_term_in_conc term :=
  change (block term) with term.
Ltac block_hyp H :=
  let tH := type of H in change tH with (block tH) in (type of H).
Ltac unblock_hyp H := idtac;
  lazymatch type of H with
  | block ?T => change (block T) with T in (type of H)
  end.
Ltac unblock_in_hyp H :=
  change @block with @ublock in (type of H) at 1; unfold ublock in H.
Ltac block_def H :=
  let vH := eval cbv delta [H] in H in change vH with (block vH) in (value of H).
Ltac unblock_def H :=
  lazymatch eval cbv delta [H] in H with
  | block ?X => change (block X) with X in (value of H)
  end.
Ltac unblock_in_def H :=
  change @block with @ublock in (value of H) at 1; unfold ublock in H.
Ltac block_conc := idtac;
  lazymatch goal with |- ?G => change G with (block G) end.
Ltac unblock_conc := idtac;
  lazymatch goal with |- block ?G => change (block G) with G end.
Ltac unblock_in_conc := 
  change @block with @ublock at 1; unfold ublock.
Ltac block_hyps :=
  let rec f :=
      (lazymatch goal with
       | H : ?T |- _ => change T with (block T) in H; revert H; f; intros H
       | _ => idtac
       end)
  in f.
Ltac unblock_hyps :=
  let rec f :=
      (lazymatch goal with
       | H : _ |- _ => try unblock_hyp H; revert H; f; intros H
       | _ => idtac
       end)
  in f.
Ltac clear_all_blocks_hyp H :=
  change @block with @ublock in H; unfold ublock in H.
Ltac clear_all_hyp_blocks :=
  change @block with @ublock in *|-; unfold ublock in *|-.
Ltac clear_all_conc_blocks :=
  change @block with @ublock; unfold ublock.
Ltac clear_all_blocks :=
  change @block with @ublock in *; unfold ublock in *.
Ltac is_blocked term := idtac;
  lazymatch term with
  | block _ => idtac
  end.
Ltac has_blocks term := idtac;
  lazymatch term with
  | context [block] => idtac
  end.

  