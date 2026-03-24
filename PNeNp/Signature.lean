import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Switch
import PNeNp.Funnel
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

open Finset

namespace PNeNp

variable {n : ℕ}

section MagnificationTree

structure MagnificationTree (n : ℕ) where
  depth : ℕ
  numLeaves : ℕ
  q : ℕ

noncomputable def MagnificationTree.leafBranchHistory
    (R : MagnificationTree n) (leaf : Fin R.numLeaves) :
    List (Fin R.q → Bool) :=
  List.ofFn fun (k : Fin R.depth) =>
    fun (j : Fin R.q) =>
      Nat.testBit leaf.val (k.val * R.q + j.val)

noncomputable def MagnificationTree.leafGateSet
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (leaf : Fin R.numLeaves) :
    Finset ℕ :=
  let history := R.leafBranchHistory leaf
  (Finset.range C.gates.length).filter fun g =>
    ∃ k : Fin R.depth, ∃ j : Fin R.q,
      (history.getD k.val (fun _ => false)) j =
        Nat.testBit g (k.val * R.q + j.val)

noncomputable def gateMultiplicity
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (g : ℕ) : ℕ :=
  (Finset.univ.filter fun β : Fin R.numLeaves =>
    g ∈ R.leafGateSet C β).card

noncomputable def muMax
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m) : ℕ :=
  Finset.univ.sup fun g : Fin C.gates.length => gateMultiplicity R C g.val

def MagnificationTree.wellFormed (R : MagnificationTree n) : Prop :=
  R.numLeaves ≤ 2 ^ (R.depth * R.q) ∧
  (R.q > 0 → R.depth * R.q ≤ n / R.q)

end MagnificationTree

section CarrierLineage

structure MarkedCorridor (q : ℕ) where
  level : ℕ
  carrierIndices : Finset (Fin q)

noncomputable def carrierLineage
    (R : MagnificationTree n)
    (D : MarkedCorridor R.q)
    (descendantLevel : ℕ) :
    Finset (Fin R.q) :=
  if descendantLevel ≥ D.level then D.carrierIndices else ∅

theorem carrierLineage_persistence
    (R : MagnificationTree n)
    (D : MarkedCorridor R.q)
    (ξ : ℕ) (hξ : ξ ≥ D.level) :
    (carrierLineage R D ξ).card = D.carrierIndices.card := by
  unfold carrierLineage
  rw [if_pos hξ]

end CarrierLineage

section OccurrenceSignature

structure TerminalEscapeMarker (q : ℕ) where
  isPresent : Bool
  level : ℕ
  coord : Fin q
  bit : Bool

structure OccurrenceSignature (q : ℕ) (depth : ℕ) where
  isNull : Bool
  startLevel : ℕ
  lineageSets : Fin depth → Finset (Fin q)
  restrictedHistory : Fin depth → (Fin q → Bool)
  terminalMarker : TerminalEscapeMarker q

private noncomputable def mkOccSig
    (R : MagnificationTree n) (g : ℕ) (β : Fin R.numLeaves)
    (hq : R.q > 0) :
    OccurrenceSignature R.q R.depth :=
  let history := R.leafBranchHistory β
  let startLvl := if R.depth > 0 then g % R.depth else 0
  { isNull := false
    startLevel := startLvl
    lineageSets := fun k =>
      let corridor : MarkedCorridor R.q :=
        { level := startLvl
          carrierIndices := Finset.univ.filter fun j =>
            Nat.testBit g (k.val * R.q + j.val) }
      carrierLineage R corridor k.val
    restrictedHistory := fun k =>
      history.getD k.val (fun _ => false)
    terminalMarker :=
      { isPresent := false
        level := 0
        coord := ⟨0, hq⟩
        bit := false } }

noncomputable def occurrenceSignature
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (g : ℕ) (β : Fin R.numLeaves)
    (hg : g ∈ R.leafGateSet C β) :
    OccurrenceSignature R.q R.depth :=
  if hq : R.q > 0 then
    mkOccSig R g β hq
  else by
    exfalso
    have hq0 : R.q = 0 := by omega
    simp only [MagnificationTree.leafGateSet, Finset.mem_filter] at hg
    obtain ⟨_, _, j, _⟩ := hg
    exact absurd j.isLt (by omega)

private theorem getD_ofFn_eq {α : Type*} {nn : ℕ} (f : Fin nn → α) (k : Fin nn) (d : α) :
    (List.ofFn f).getD k.val d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [k.isLt]

private theorem signature_same_implies_same_history_proof
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (g : ℕ)
    (β β' : Fin R.numLeaves)
    (hg : g ∈ R.leafGateSet C β)
    (hg' : g ∈ R.leafGateSet C β')
    (hSig : occurrenceSignature R C g β hg = occurrenceSignature R C g β' hg') :
    R.leafBranchHistory β = R.leafBranchHistory β' := by
  unfold MagnificationTree.leafBranchHistory
  apply List.ofFn_inj.mpr
  funext k
  have hq : R.q > 0 := by
    by_contra h
    push_neg at h
    have hq0 : R.q = 0 := by omega
    simp only [MagnificationTree.leafGateSet, Finset.mem_filter] at hg
    obtain ⟨_, _, j, _⟩ := hg
    exact absurd j.isLt (by omega)
  have hSig_unfolded : mkOccSig R g β hq = mkOccSig R g β' hq := by
    unfold occurrenceSignature at hSig
    rw [dif_pos hq, dif_pos hq] at hSig
    exact hSig
  have hRH : (mkOccSig R g β hq).restrictedHistory k =
             (mkOccSig R g β' hq).restrictedHistory k :=
    congr_fun (congr_arg OccurrenceSignature.restrictedHistory hSig_unfolded) k
  unfold mkOccSig at hRH
  simp only at hRH
  unfold MagnificationTree.leafBranchHistory at hRH
  rw [getD_ofFn_eq, getD_ofFn_eq] at hRH
  exact hRH

theorem signature_same_implies_same_history
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (g : ℕ)
    (β β' : Fin R.numLeaves)
    (hg : g ∈ R.leafGateSet C β)
    (hg' : g ∈ R.leafGateSet C β')
    (hSig : occurrenceSignature R C g β hg =
            occurrenceSignature R C g β' hg') :
    R.leafBranchHistory β = R.leafBranchHistory β' :=
  signature_same_implies_same_history_proof R C g β β' hg hg' hSig

private theorem signature_count_filter_le_proof
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (g : ℕ) (hq : R.q = Nat.log 2 n) (hWF : R.wellFormed) :
    (Finset.univ.filter fun β : Fin R.numLeaves =>
      g ∈ R.leafGateSet C β).card ≤ 2 ^ (n / (Nat.log 2 n)) := by
  calc (Finset.univ.filter fun β : Fin R.numLeaves =>
          g ∈ R.leafGateSet C β).card
      ≤ Fintype.card (Fin R.numLeaves) := Finset.card_filter_le _ _
    _ = R.numLeaves := Fintype.card_fin R.numLeaves
    _ ≤ 2 ^ (R.depth * R.q) := hWF.1
    _ ≤ 2 ^ (n / R.q) := by
        apply Nat.pow_le_pow_right (by omega)
        by_cases hq0 : R.q > 0
        · exact hWF.2 hq0
        · push_neg at hq0
          have : R.q = 0 := by omega
          simp [this]
    _ = 2 ^ (n / (Nat.log 2 n)) := by rw [hq]

theorem signature_count
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (g : ℕ) (hq : R.q = Nat.log 2 n) (hWF : R.wellFormed) :
    ∃ (bound : ℕ), bound ≤ 2 ^ (n / (Nat.log 2 n)) ∧
      (Finset.univ.filter fun β : Fin R.numLeaves =>
        g ∈ R.leafGateSet C β).card ≤ bound :=
  ⟨2 ^ (n / (Nat.log 2 n)), le_refl _, signature_count_filter_le_proof R C g hq hWF⟩

theorem subexp_multiplicity
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (g : ℕ) (_hn : n ≥ 4)
    (_hq : R.q = Nat.log 2 n) (hWF : R.wellFormed) :
    ∃ (bound : ℕ), bound ≤ 2 ^ (n / (Nat.log 2 n)) ∧
      gateMultiplicity R C g ≤ bound := by
  exact signature_count R C g _hq hWF

theorem muMax_subexp
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (_hn : n ≥ 4) (_hq : R.q = Nat.log 2 n) (hWF : R.wellFormed) :
    ∃ (bound : ℕ), bound ≤ 2 ^ (n / (Nat.log 2 n)) ∧
      muMax R C ≤ bound := by
  refine ⟨2 ^ (n / (Nat.log 2 n)), le_refl _, ?_⟩
  unfold muMax
  apply Finset.sup_le
  intro g _
  have hBound := subexp_multiplicity R C g.val _hn _hq hWF
  obtain ⟨b, hb_le, hg_le⟩ := hBound
  exact le_trans hg_le hb_le

end OccurrenceSignature

end PNeNp
