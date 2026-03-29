import PNeNp.Robustness
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Finset

namespace PNeNp

section HamCycleCountScaffold

variable {n : ℕ}

noncomputable def numPathComponents (F : Finset (Edge n)) : ℕ :=
  (incidentVertices F).card - F.card

@[simp] lemma numPathComponents_def (F : Finset (Edge n)) :
    numPathComponents F = (incidentVertices F).card - F.card := rfl

@[simp] lemma numPathComponents_empty :
    numPathComponents (n := n) (∅ : Finset (Edge n)) = 0 := by
  simp [numPathComponents, incidentVertices]

@[simp] lemma numPathComponents_nonneg (F : Finset (Edge n)) :
    0 ≤ numPathComponents F := by
  exact Nat.zero_le _

theorem restrictedHamCycles_mem_of_relabel_forcedPresent (hn : n ≥ 4)
    (F : Finset (Edge n)) (σ : Equiv.Perm (Fin n))
    (hF : F ⊆ relabelEdges σ (canonEdges n (by omega))) :
    relabelEdges σ (canonEdges n (by omega)) ∈
      restrictedHamCycles n ⟨F, (∅ : Finset (Edge n))⟩ := by
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hF, ?_, isHamCycle_relabel hn σ _ (canonicalCycleIsHam hn)⟩
  simp

theorem fintype_card_le_restrictedHamCycles_card_of_injective_family
    {α : Type*} [Fintype α]
    (ρ : Restriction n)
    (f : α → Finset (Edge n))
    (hf : ∀ a, f a ∈ restrictedHamCycles n ρ)
    (hinj : Function.Injective f) :
    Fintype.card α ≤ (restrictedHamCycles n ρ).card := by
  classical
  let g : α → ↥(restrictedHamCycles n ρ) := fun a => ⟨f a, hf a⟩
  have hginj : Function.Injective g := by
    intro a b h
    apply hinj
    exact congrArg Subtype.val h
  simpa using Fintype.card_le_of_injective g hginj

theorem forcedPresent_lower_bound_from_relabel_family
    {α : Type*} [Fintype α]
    (hn : n ≥ 4)
    (F : Finset (Edge n))
    (σ : α → Equiv.Perm (Fin n))
    (hpres : ∀ a, F ⊆ relabelEdges (σ a) (canonEdges n (by omega)))
    (hinj : Function.Injective (fun a => relabelEdges (σ a) (canonEdges n (by omega)))) :
    Fintype.card α ≤ (restrictedHamCycles n ⟨F, (∅ : Finset (Edge n))⟩).card := by
  classical
  refine
    fintype_card_le_restrictedHamCycles_card_of_injective_family (n := n)
      ⟨F, (∅ : Finset (Edge n))⟩
      (fun a => relabelEdges (σ a) (canonEdges n (by omega)))
      ?_ hinj
  intro a
  exact restrictedHamCycles_mem_of_relabel_forcedPresent (n := n) hn F (σ a) (hpres a)

theorem restrictedHamCycles_forcedPresent_card_lower_of_family
    {α : Type*} [Fintype α]
    (hn : n ≥ 4)
    (ρ : Restriction n)
    (hcard :
      2 ^ (numPathComponents ρ.forcedPresent) *
        (Nat.factorial (n - ρ.forcedPresent.card - 1) / 2)
        ≤ Fintype.card α)
    (σ : α → Equiv.Perm (Fin n))
    (hpres : ∀ a, ρ.forcedPresent ⊆ relabelEdges (σ a) (canonEdges n (by omega)))
    (hinj : Function.Injective (fun a => relabelEdges (σ a) (canonEdges n (by omega)))) :
    2 ^ (numPathComponents ρ.forcedPresent) *
      (Nat.factorial (n - ρ.forcedPresent.card - 1) / 2)
      ≤ (restrictedHamCycles n ⟨ρ.forcedPresent, (∅ : Finset (Edge n))⟩).card := by
  exact le_trans hcard
    (forcedPresent_lower_bound_from_relabel_family (n := n) hn ρ.forcedPresent σ hpres hinj)

end HamCycleCountScaffold

section HamCycleCountCandidateFamily

variable {n : ℕ}

abbrev CandidateFamily (ρ : Restriction n) : Type :=
  (Fin (numPathComponents ρ.forcedPresent) → Bool) ×
    Equiv.Perm (Fin (n - ρ.forcedPresent.card - 1))

theorem card_candidateFamily (ρ : Restriction n) :
    Fintype.card (CandidateFamily (n := n) ρ) =
      2 ^ (numPathComponents ρ.forcedPresent) *
        Nat.factorial (n - ρ.forcedPresent.card - 1) := by
  simp [CandidateFamily, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_bool]

theorem candidateFamily_target_le_card (ρ : Restriction n) :
    2 ^ (numPathComponents ρ.forcedPresent) *
      (Nat.factorial (n - ρ.forcedPresent.card - 1) / 2)
      ≤ Fintype.card (CandidateFamily (n := n) ρ) := by
  rw [card_candidateFamily]
  exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)

def LinearStepCompatible (F : Finset (Edge n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ e ∈ F, ∃ u v : Fin n, ∃ k : ℕ, ∃ hk : k + 1 < n,
    e = Sym2.mk (u, v) ∧
    σ.symm u = ⟨k, by omega⟩ ∧
    σ.symm v = ⟨k + 1, hk⟩

theorem linearStepCompatible_subset_relabel (hn : n ≥ 4)
    {F : Finset (Edge n)} {σ : Equiv.Perm (Fin n)}
    (hcomp : LinearStepCompatible (n := n) F σ) :
    F ⊆ relabelEdges σ (canonEdges n (by omega)) := by
  intro e he
  rcases hcomp e he with ⟨u, v, k, hk, rfl, hu, hv⟩
  rw [mk_mem_relabelEdges_iff]
  rw [hu, hv]
  exact canonEdges_step_mem (n := n) hn k hk

theorem exists_forcedPresent_relabel_family_of_candidateMap (hn : n ≥ 4)
    (ρ : Restriction n)
    (σ : CandidateFamily (n := n) ρ → Equiv.Perm (Fin n))
    (hcomp : ∀ a, LinearStepCompatible (n := n) ρ.forcedPresent (σ a))
    (hinj : Function.Injective
      (fun a => relabelEdges (σ a) (canonEdges n (by omega)))) :
    ∃ (α : Type) (_ : Fintype α),
      2 ^ (numPathComponents ρ.forcedPresent) *
        (Nat.factorial (n - ρ.forcedPresent.card - 1) / 2)
        ≤ @Fintype.card α ‹_› ∧
      ∃ τ : α → Equiv.Perm (Fin n),
        (∀ a, ρ.forcedPresent ⊆ relabelEdges (τ a) (canonEdges n (by omega))) ∧
        Function.Injective (fun a => relabelEdges (τ a) (canonEdges n (by omega))) := by
  refine ⟨CandidateFamily (n := n) ρ, inferInstance, ?_, ?_⟩
  · exact candidateFamily_target_le_card (n := n) ρ
  · refine ⟨σ, ?_, hinj⟩
    intro a
    exact linearStepCompatible_subset_relabel (n := n) hn (hcomp a)

theorem restrictedHamCycles_forcedPresent_card_lower_of_candidateMap (hn : n ≥ 4)
    (ρ : Restriction n)
    (σ : CandidateFamily (n := n) ρ → Equiv.Perm (Fin n))
    (hcomp : ∀ a, LinearStepCompatible (n := n) ρ.forcedPresent (σ a))
    (hinj : Function.Injective
      (fun a => relabelEdges (σ a) (canonEdges n (by omega)))) :
    2 ^ (numPathComponents ρ.forcedPresent) *
      (Nat.factorial (n - ρ.forcedPresent.card - 1) / 2)
      ≤ (restrictedHamCycles n ⟨ρ.forcedPresent, (∅ : Finset (Edge n))⟩).card := by
  exact restrictedHamCycles_forcedPresent_card_lower_of_family
    (α := CandidateFamily (n := n) ρ) (n := n) hn ρ
    (candidateFamily_target_le_card (n := n) ρ) σ
    (fun a => linearStepCompatible_subset_relabel (n := n) hn (hcomp a))
    hinj

end HamCycleCountCandidateFamily

section PathForestLocal

variable {n : ℕ}

def forcedDeg (ρ : Restriction n) (v : Fin n) : ℕ :=
  (ρ.forcedPresent.filter fun e => v ∈ e).card

@[simp] lemma forcedDeg_def (ρ : Restriction n) (v : Fin n) :
    forcedDeg ρ v = (ρ.forcedPresent.filter fun e => v ∈ e).card := rfl

lemma mem_incidentVertices_iff {F : Finset (Edge n)} {v : Fin n} :
    v ∈ incidentVertices F ↔ 0 < (F.filter fun e => v ∈ e).card := by
  simp [incidentVertices]

lemma forcedDeg_pos_iff_mem_incidentVertices (ρ : Restriction n) (v : Fin n) :
    0 < forcedDeg ρ v ↔ v ∈ incidentVertices ρ.forcedPresent := by
  rw [forcedDeg_def, mem_incidentVertices_iff]

lemma forcedPresent_noLoops (ρ : Restriction n) (hpath : ρ.isPathCompatible) :
    ∀ e ∈ ρ.forcedPresent, ¬ e.IsDiag := by
  rcases hpath with ⟨_, hloops, _⟩
  exact hloops

lemma forcedDeg_le_two (ρ : Restriction n) (hpath : ρ.isPathCompatible) (v : Fin n) :
    forcedDeg ρ v ≤ 2 := by
  rcases hpath with ⟨hdeg, _, _⟩
  have hsup :
      forcedDeg ρ v ≤
        Finset.univ.sup (fun w : Fin n =>
          (ρ.forcedPresent.filter fun e => w ∈ e).card) := by
    simpa [forcedDeg] using
      (Finset.le_sup (s := Finset.univ)
        (f := fun w : Fin n => (ρ.forcedPresent.filter fun e => w ∈ e).card)
        (by simp : v ∈ Finset.univ))
  simpa [Restriction.maxDegree, forcedDeg] using le_trans hsup hdeg

lemma forcedDeg_eq_one_or_two_of_incident
    (ρ : Restriction n) (hpath : ρ.isPathCompatible) (v : Fin n)
    (hv : v ∈ incidentVertices ρ.forcedPresent) :
    forcedDeg ρ v = 1 ∨ forcedDeg ρ v = 2 := by
  have hpos : 0 < forcedDeg ρ v := (forcedDeg_pos_iff_mem_incidentVertices ρ v).2 hv
  have hle : forcedDeg ρ v ≤ 2 := forcedDeg_le_two ρ hpath v
  omega

lemma edge_endpoint_mem_incident_left
    (ρ : Restriction n) {u v : Fin n}
    (he : Sym2.mk (u, v) ∈ ρ.forcedPresent) :
    u ∈ incidentVertices ρ.forcedPresent := by
  rw [mem_incidentVertices_iff]
  have hmem : Sym2.mk (u, v) ∈ ρ.forcedPresent.filter (fun e => u ∈ e) := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨he, by simp [Sym2.mem_iff]⟩
  exact Finset.card_pos.mpr ⟨_, hmem⟩

lemma edge_endpoint_mem_incident_right
    (ρ : Restriction n) {u v : Fin n}
    (he : Sym2.mk (u, v) ∈ ρ.forcedPresent) :
    v ∈ incidentVertices ρ.forcedPresent := by
  rw [mem_incidentVertices_iff]
  have hmem : Sym2.mk (u, v) ∈ ρ.forcedPresent.filter (fun e => v ∈ e) := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨he, by simp [Sym2.mem_iff]⟩
  exact Finset.card_pos.mpr ⟨_, hmem⟩

lemma edge_endpoints_ne
    (ρ : Restriction n) (hpath : ρ.isPathCompatible)
    {u v : Fin n}
    (he : Sym2.mk (u, v) ∈ ρ.forcedPresent) :
    u ≠ v := by
  have hnd := forcedPresent_noLoops ρ hpath (Sym2.mk (u, v)) he
  rw [Sym2.mk_isDiag_iff] at hnd
  exact hnd

end PathForestLocal

section ExpandPerm

variable {n : ℕ}

private def liftSucc (hn : n ≥ 1) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by omega⟩

private lemma liftSucc_injective (hn : n ≥ 1) : Function.Injective (liftSucc hn : Fin (n - 1) → Fin n) := by
  intro a b h
  simp [liftSucc, Fin.ext_iff] at h
  exact Fin.ext h

private def dropSucc (hn : n ≥ 1) (i : Fin n) (hi : i.val ≥ 1) : Fin (n - 1) :=
  ⟨i.val - 1, by omega⟩

private lemma liftSucc_dropSucc (hn : n ≥ 1) (i : Fin n) (hi : i.val ≥ 1) :
    liftSucc hn (dropSucc hn i hi) = i := by
  simp [liftSucc, dropSucc, Fin.ext_iff]; omega

private lemma liftSucc_val_ne_zero (hn : n ≥ 1) (i : Fin (n - 1)) :
    (liftSucc hn i).val ≠ 0 := by
  simp [liftSucc]

private lemma liftSucc_val_ge_one (hn : n ≥ 1) (i : Fin (n - 1)) :
    (liftSucc hn i).val ≥ 1 := by
  simp [liftSucc]

private lemma dropSucc_liftSucc (hn : n ≥ 1) (i : Fin (n - 1)) :
    dropSucc hn (liftSucc hn i) (liftSucc_val_ge_one hn i) = i := by
  simp [liftSucc, dropSucc]

noncomputable def expandPermFixZero (hn : n ≥ 1) (τ : Equiv.Perm (Fin (n - 1))) :
    Equiv.Perm (Fin n) where
  toFun i :=
    if hi : i.val = 0 then ⟨0, by omega⟩
    else liftSucc hn (τ (dropSucc hn i (by omega)))
  invFun i :=
    if hi : i.val = 0 then ⟨0, by omega⟩
    else liftSucc hn (τ.symm (dropSucc hn i (by omega)))
  left_inv i := by
    simp only
    by_cases hi : i.val = 0
    · simp [hi, Fin.ext_iff]
    · simp only [hi, dite_false]
      have hne := liftSucc_val_ne_zero hn (τ (dropSucc hn i (by omega)))
      simp only [hne, dite_false, dropSucc_liftSucc, Equiv.symm_apply_apply,
        liftSucc_dropSucc]
  right_inv i := by
    simp only
    by_cases hi : i.val = 0
    · simp [hi, Fin.ext_iff]
    · simp only [hi, dite_false]
      have hne := liftSucc_val_ne_zero hn (τ.symm (dropSucc hn i (by omega)))
      simp only [hne, dite_false, dropSucc_liftSucc, Equiv.apply_symm_apply,
        liftSucc_dropSucc]

theorem expandPermFixZero_apply_zero (hn : n ≥ 1) (τ : Equiv.Perm (Fin (n - 1))) :
    expandPermFixZero hn τ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  simp [expandPermFixZero]

theorem expandPermFixZero_apply_succ (hn : n ≥ 1) (τ : Equiv.Perm (Fin (n - 1)))
    (i : Fin (n - 1)) :
    expandPermFixZero hn τ (liftSucc hn i) = liftSucc hn (τ i) := by
  simp [expandPermFixZero, liftSucc_val_ne_zero hn i, dropSucc_liftSucc]

theorem expandPermFixZero_injective (hn : n ≥ 1) :
    Function.Injective (expandPermFixZero hn) := by
  intro τ₁ τ₂ h
  ext i
  have h' := Equiv.ext_iff.mp h (liftSucc hn i)
  rw [expandPermFixZero_apply_succ, expandPermFixZero_apply_succ] at h'
  have := liftSucc_injective hn h'
  exact congrArg Fin.val this

theorem expandPermFixZero_symm_apply_zero (hn : n ≥ 1) (τ : Equiv.Perm (Fin (n - 1))) :
    (expandPermFixZero hn τ).symm ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  have h := expandPermFixZero_apply_zero hn τ
  rw [Equiv.symm_apply_eq]; exact h.symm

theorem linearStepCompatible_empty (σ : Equiv.Perm (Fin n)) :
    LinearStepCompatible (n := n) ∅ σ := by
  intro e he
  simp at he

end ExpandPerm

section RealizePath

variable {n : ℕ}

theorem relabelEdges_id (H : Finset (Edge n)) :
    relabelEdges (Equiv.refl (Fin n)) H = H := by
  unfold relabelEdges
  ext e
  simp [Function.Embedding.sym2Map, Equiv.toEmbedding]

theorem relabelEdges_symm_eq (σ : Equiv.Perm (Fin n)) (H : Finset (Edge n)) :
    relabelEdges σ.symm (relabelEdges σ H) = H := by
  unfold relabelEdges
  simp only [Finset.map_map]
  ext e
  simp [Function.Embedding.sym2Map, Equiv.toEmbedding, Sym2.map_map, Function.comp]

theorem relabelEdges_injective_perm (σ : Equiv.Perm (Fin n)) :
    Function.Injective (relabelEdges σ : Finset (Edge n) → Finset (Edge n)) := by
  intro A B h
  have := congr_arg (relabelEdges σ.symm) h
  rwa [relabelEdges_symm_eq, relabelEdges_symm_eq] at this

theorem restrictedHamCycles_forcedPresent_only_nonempty_of_realize (hn : n ≥ 4)
    (F : Finset (Edge n))
    (σ : Equiv.Perm (Fin n))
    (hF : F ⊆ relabelEdges σ (canonEdges n (by omega))) :
    (restrictedHamCycles n ⟨F, (∅ : Finset (Edge n))⟩).Nonempty := by
  exact ⟨_, restrictedHamCycles_mem_of_relabel_forcedPresent hn F σ hF⟩

theorem emptyForced_realize (hn : n ≥ 4) :
    (∅ : Finset (Edge n)) ⊆
      relabelEdges (Equiv.refl (Fin n)) (canonEdges n (by omega)) := by
  exact Finset.empty_subset _

theorem restrictedHamCycles_empty_forced_nonempty (hn : n ≥ 4) :
    (restrictedHamCycles n ⟨∅, (∅ : Finset (Edge n))⟩).Nonempty :=
  restrictedHamCycles_forcedPresent_only_nonempty_of_realize hn ∅
    (Equiv.refl (Fin n)) (emptyForced_realize hn)

end RealizePath

section RelabelEdgesProps

variable {n : ℕ}

theorem relabelEdges_comp (σ₁ σ₂ : Equiv.Perm (Fin n)) (H : Finset (Edge n)) :
    relabelEdges σ₁ (relabelEdges σ₂ H) = relabelEdges (σ₁ * σ₂) H := by
  unfold relabelEdges
  simp only [Finset.map_map]
  congr 1
  ext e
  simp [Function.Embedding.sym2Map, Equiv.toEmbedding, Sym2.map_map, Function.comp,
    Equiv.Perm.coe_mul]

theorem relabelEdges_card (σ : Equiv.Perm (Fin n)) (H : Finset (Edge n)) :
    (relabelEdges σ H).card = H.card := by
  unfold relabelEdges
  exact Finset.card_map _

end RelabelEdgesProps

section ForcedPresentRealize

variable {n : ℕ}

theorem restrictedHamCycles_forcedPresent_only_card_lower (hn : n ≥ 4)
    (F : Finset (Edge n))
    (family : Finset (Equiv.Perm (Fin n)))
    (hpres : ∀ σ ∈ family, F ⊆ relabelEdges σ (canonEdges n (by omega)))
    (hinj : ∀ σ₁ ∈ family, ∀ σ₂ ∈ family,
      relabelEdges σ₁ (canonEdges n (by omega)) =
      relabelEdges σ₂ (canonEdges n (by omega)) → σ₁ = σ₂) :
    family.card ≤ (restrictedHamCycles n ⟨F, (∅ : Finset (Edge n))⟩).card := by
  classical
  let f : Equiv.Perm (Fin n) → Finset (Edge n) :=
    fun σ => relabelEdges σ (canonEdges n (by omega))
  have hf_mem : ∀ σ ∈ family, f σ ∈ restrictedHamCycles n ⟨F, (∅ : Finset (Edge n))⟩ := by
    intro σ hσ
    exact restrictedHamCycles_mem_of_relabel_forcedPresent hn F σ (hpres σ hσ)
  have hf_inj : Set.InjOn f ↑family := by
    intro σ₁ hσ₁ σ₂ hσ₂ heq
    exact hinj σ₁ hσ₁ σ₂ hσ₂ heq
  calc family.card = (family.image f).card := by
        rw [Finset.card_image_of_injOn hf_inj]
    _ ≤ (restrictedHamCycles n ⟨F, (∅ : Finset (Edge n))⟩).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp he
        exact hf_mem σ hσ

end ForcedPresentRealize

section ExpandCandidate

variable {n : ℕ}

noncomputable def expandCandidateToPermEmpty (hn : n ≥ 4)
    (τ : Equiv.Perm (Fin (n - 1))) : Equiv.Perm (Fin n) :=
  expandPermFixZero (by omega) τ

theorem expandCandidateToPermEmpty_subset (hn : n ≥ 4)
    (τ : Equiv.Perm (Fin (n - 1))) :
    (∅ : Finset (Edge n)) ⊆
      relabelEdges (expandCandidateToPermEmpty hn τ) (canonEdges n (by omega)) :=
  Finset.empty_subset _

theorem relabelEdges_perm_injective (hn : n ≥ 4)
    (σ₁ σ₂ : Equiv.Perm (Fin n))
    (h : relabelEdges σ₁ (canonEdges n (by omega)) =
         relabelEdges σ₂ (canonEdges n (by omega))) :
    ∀ e ∈ canonEdges n (by omega),
      Sym2.map σ₁ e ∈ relabelEdges σ₂ (canonEdges n (by omega)) := by
  intro e he
  rw [← h]
  exact Finset.mem_map.mpr ⟨e, he, rfl⟩

end ExpandCandidate

section CountingBound

variable {n : ℕ}

theorem restrictedHamCycles_empty_card_pos (hn : n ≥ 4) :
    0 < (restrictedHamCycles n ⟨∅, (∅ : Finset (Edge n))⟩).card :=
  Finset.card_pos.mpr (restrictedHamCycles_empty_forced_nonempty hn)

theorem empty_restriction_all_hamcycles (_hn : n ≥ 4) (H : Finset (Edge n))
    (hH : IsHamCycle n H) :
    H ∈ restrictedHamCycles n ⟨∅, (∅ : Finset (Edge n))⟩ := by
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨Finset.empty_subset _, Finset.disjoint_empty_left _, hH⟩

theorem relabel_gives_hamcycle_in_empty_restriction (hn : n ≥ 4)
    (σ : Equiv.Perm (Fin n)) :
    relabelEdges σ (canonEdges n (by omega)) ∈
      restrictedHamCycles n ⟨∅, (∅ : Finset (Edge n))⟩ :=
  empty_restriction_all_hamcycles hn _ (isHamCycle_relabel hn σ _ (canonicalCycleIsHam hn))

theorem perm_relabel_image_subset_restricted (hn : n ≥ 4) :
    (Finset.univ.image (fun σ : Equiv.Perm (Fin n) =>
      relabelEdges σ (canonEdges n (by omega)))) ⊆
    restrictedHamCycles n ⟨∅, (∅ : Finset (Edge n))⟩ := by
  intro H hH
  obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hH
  exact relabel_gives_hamcycle_in_empty_restriction hn σ

theorem relabel_image_card_le_restricted (hn : n ≥ 4) :
    (Finset.univ.image (fun σ : Equiv.Perm (Fin n) =>
      relabelEdges σ (canonEdges n (by omega)))).card ≤
    (restrictedHamCycles n ⟨∅, (∅ : Finset (Edge n))⟩).card :=
  Finset.card_le_card (perm_relabel_image_subset_restricted hn)

end CountingBound

section CycleTraversal

variable {n : ℕ}

theorem canonEdges_symm_neighbor_unique (hn : n ≥ 4) (σ : Equiv.Perm (Fin n))
    (k : Fin n) (hk : k.val + 1 < n) :
    Sym2.mk (σ k, σ ⟨k.val + 1, hk⟩) ∈ relabelEdges σ (canonEdges n (by omega)) := by
  rw [mk_mem_relabelEdges_iff]
  simp
  exact canonEdges_step_mem hn k.val hk

theorem expandPermFixZero_preserves_step (hn : n ≥ 4)
    (τ : Equiv.Perm (Fin (n - 1))) (k : Fin (n - 1)) (hk : k.val + 1 < n - 1) :
    Sym2.mk (liftSucc (by omega : n ≥ 1) (τ k),
             liftSucc (by omega : n ≥ 1) (τ ⟨k.val + 1, by omega⟩)) ∈
      relabelEdges (expandPermFixZero (by omega : n ≥ 1) τ) (canonEdges n (by omega)) := by
  have h1 := expandPermFixZero_apply_succ (by omega : n ≥ 1) τ k
  have h2 := expandPermFixZero_apply_succ (by omega : n ≥ 1) τ ⟨k.val + 1, by omega⟩
  rw [← h1, ← h2]
  have hls1 : liftSucc (by omega : n ≥ 1) k = ⟨k.val + 1, by omega⟩ := by
    simp [liftSucc]
  have hls2 : liftSucc (by omega : n ≥ 1) ⟨k.val + 1, by omega⟩ = ⟨k.val + 2, by omega⟩ := by
    simp [liftSucc]
  rw [hls1, hls2]
  exact canonEdges_symm_neighbor_unique hn (expandPermFixZero (by omega) τ)
    ⟨k.val + 1, by omega⟩ (by omega : k.val + 1 + 1 < n)

theorem expandPermFixZero_first_edge (hn : n ≥ 4)
    (τ : Equiv.Perm (Fin (n - 1))) (hn1 : 0 < n - 1) :
    Sym2.mk (⟨0, by omega⟩, liftSucc (by omega : n ≥ 1) (τ ⟨0, hn1⟩)) ∈
      relabelEdges (expandPermFixZero (by omega : n ≥ 1) τ) (canonEdges n (by omega)) := by
  have h0 := expandPermFixZero_apply_zero (by omega : n ≥ 1) τ
  have h1 := expandPermFixZero_apply_succ (by omega : n ≥ 1) τ ⟨0, hn1⟩
  rw [← h0, ← h1]
  have hls : liftSucc (by omega : n ≥ 1) ⟨0, hn1⟩ = ⟨1, by omega⟩ := by
    simp [liftSucc]
  rw [hls]
  exact canonEdges_symm_neighbor_unique hn (expandPermFixZero (by omega) τ)
    ⟨0, by omega⟩ (by omega : 0 + 1 < n)

end CycleTraversal

section PathForestRealize

/-! ### Path forest realizability

A path forest (set of edges with max degree ≤ 2, no loops, no cycles,
fewer edges than vertices) can always be embedded as consecutive
edges of a Hamiltonian cycle on Fin n. Equivalently, there exists a
permutation σ such that every forced edge maps to a canonical step.

The proof is by strong induction on |F|. In each step we remove a
leaf edge (one whose endpoint has degree 1 in F), apply the IH,
then reinsert via a segment reversal (2-opt move) that preserves
all previously placed edges.
-/

variable {n : ℕ}

private lemma single_edge_in_canonEdges (hn : n ≥ 4)
    (u v : Fin n) (huv : u ≠ v) :
    ∃ σ : Equiv.Perm (Fin n),
      Sym2.mk (u, v) ∈ relabelEdges σ (canonEdges n (by omega)) := by
  let σ := (Equiv.swap (⟨0, by omega⟩ : Fin n) u) *
    (Equiv.swap (⟨1, by omega⟩ : Fin n)
      ((Equiv.swap (⟨0, by omega⟩ : Fin n) u) v))
  refine ⟨σ, ?_⟩
  rw [mk_mem_relabelEdges_iff]
  set w := Equiv.swap (⟨0, by omega⟩ : Fin n) u v with hw_def
  have hw_ne_zero : w ≠ ⟨0, by omega⟩ := by
    rw [hw_def]; intro h
    apply huv
    have hinj := (Equiv.swap (⟨0, by omega⟩ : Fin n) u).injective
    apply hinj
    rw [h, Equiv.swap_apply_right]
  have hone_ne_zero : (⟨1, by omega⟩ : Fin n) ≠ (⟨0, by omega⟩ : Fin n) := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  have h0 : σ.symm u = ⟨0, by omega⟩ := by
    show (Equiv.swap (⟨1, by omega⟩ : Fin n) w *
      Equiv.swap (⟨0, by omega⟩ : Fin n) u) u = ⟨0, by omega⟩
    simp only [Equiv.Perm.coe_mul, Function.comp, Equiv.swap_apply_right]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hone_ne_zero) (Ne.symm hw_ne_zero)
  have h1 : σ.symm v = ⟨1, by omega⟩ := by
    show (Equiv.swap (⟨1, by omega⟩ : Fin n) w *
      Equiv.swap (⟨0, by omega⟩ : Fin n) u) v = ⟨1, by omega⟩
    simp only [Equiv.Perm.coe_mul, Function.comp, ← hw_def]
    exact Equiv.swap_apply_right _ _
  rw [h0, h1]
  exact canonEdges_step_mem hn 0 (by omega)

private noncomputable def segReverseFun (n : ℕ) (a b : ℕ) (i : Fin n) : Fin n :=
  if h : a ≤ i.val ∧ i.val ≤ b ∧ b < n then
    ⟨a + b - i.val, by omega⟩
  else i

private lemma segReverseFun_involutive (a b : ℕ) (hab : a ≤ b) (hb : b < n) :
    ∀ i : Fin n, segReverseFun n a b (segReverseFun n a b i) = i := by
  intro i; simp only [segReverseFun]
  split
  · rename_i h
    have h1 : a ≤ a + b - i.val := by omega
    have h2 : a + b - i.val ≤ b := by omega
    simp only [show (⟨a + b - i.val, by omega⟩ : Fin n).val = a + b - i.val from rfl,
      h1, h2, hb, and_self, true_and, dite_true]
    congr 1; omega
  · rfl

private noncomputable def segReverse (n : ℕ) (a b : ℕ) (hab : a ≤ b) (hb : b < n) :
    Equiv.Perm (Fin n) where
  toFun := segReverseFun n a b
  invFun := segReverseFun n a b
  left_inv := segReverseFun_involutive a b hab hb
  right_inv := segReverseFun_involutive a b hab hb

private lemma segReverse_inside (a b : ℕ) (hab : a ≤ b) (hb : b < n)
    (i : Fin n) (ha_le : a ≤ i.val) (hi_le : i.val ≤ b) :
    (segReverse n a b hab hb) i = ⟨a + b - i.val, by omega⟩ := by
  simp only [segReverse, segReverseFun, Equiv.coe_fn_mk, ha_le, hi_le, hb, and_self, dite_true]

private lemma segReverse_outside (a b : ℕ) (hab : a ≤ b) (hb : b < n)
    (i : Fin n) (hi : i.val < a ∨ b < i.val) :
    (segReverse n a b hab hb) i = i := by
  simp only [segReverse, segReverseFun, Equiv.coe_fn_mk]
  split
  · rename_i h; omega
  · rfl

private lemma segReverse_symm_eq (a b : ℕ) (hab : a ≤ b) (hb : b < n) :
    (segReverse n a b hab hb).symm = segReverse n a b hab hb := by
  ext i; simp [segReverse]

private lemma segReverse_preserves_canon_inside (hn : n ≥ 4)
    (a b : ℕ) (hab : a ≤ b) (hb : b < n)
    (k : ℕ) (hk : k + 1 < n) (hka : a ≤ k) (hkb : k + 1 ≤ b) :
    Sym2.mk ((segReverse n a b hab hb) ⟨k, by omega⟩,
             (segReverse n a b hab hb) ⟨k + 1, hk⟩) ∈
      canonEdges n (by omega) := by
  rw [show (segReverse n a b hab hb) ⟨k, by omega⟩ =
      (⟨a + b - k, by omega⟩ : Fin n) from
    segReverse_inside a b hab hb ⟨k, by omega⟩ hka (by omega : k ≤ b)]
  rw [show (segReverse n a b hab hb) ⟨k + 1, hk⟩ =
      (⟨a + b - (k + 1), by omega⟩ : Fin n) from
    segReverse_inside a b hab hb ⟨k + 1, hk⟩ (by omega : a ≤ k + 1) hkb]
  rw [Sym2.eq_swap]
  rw [show (⟨a + b - k, by omega⟩ : Fin n) =
      (⟨a + b - (k + 1) + 1, by omega⟩ : Fin n) from
    Fin.ext (by simp only [Fin.val_mk]; omega)]
  exact canonEdges_step_mem hn (a + b - (k + 1)) (by omega)

private lemma segReverse_preserves_canon_outside (hn : n ≥ 4)
    (a b : ℕ) (hab : a ≤ b) (hb : b < n)
    (k : ℕ) (hk : k + 1 < n) (hout : k + 1 < a ∨ b < k) :
    Sym2.mk ((segReverse n a b hab hb) ⟨k, by omega⟩,
             (segReverse n a b hab hb) ⟨k + 1, hk⟩) ∈
      canonEdges n (by omega) := by
  have hk_val : (⟨k, by omega⟩ : Fin n).val = k := rfl
  have hk1_val : (⟨k + 1, hk⟩ : Fin n).val = k + 1 := rfl
  rw [segReverse_outside a b hab hb ⟨k, by omega⟩
      (by rw [hk_val]; omega)]
  rw [segReverse_outside a b hab hb ⟨k + 1, hk⟩
      (by rw [hk1_val]; omega)]
  exact canonEdges_step_mem hn k hk

private lemma subset_relabelEdges_insert_of_deg0 (hn : n ≥ 4)
    (G' : Finset (Edge n)) (a b : Fin n) (hab : a ≠ b)
    (σ' : Equiv.Perm (Fin n)) (hσ' : G' ⊆ relabelEdges σ' (canonEdges n (by omega)))
    (ha_deg0 : (G'.filter fun e => a ∈ e).card = 0)
    (hb_deg : (G'.filter fun e => b ∈ e).card ≤ 1) :
    ∃ σ : Equiv.Perm (Fin n),
      insert (Sym2.mk (a, b)) G' ⊆ relabelEdges σ (canonEdges n (by omega)) := by
  -- Positions of a, b under σ'
  set pa := σ'.symm a with hpa_def
  set pb := σ'.symm b with hpb_def
  have hpa_ne_pb : pa ≠ pb := by
    intro h; exact hab (σ'.symm.injective h)
  -- a has no G' edges: both canonical neighbors of pa are free
  have ha_free : ∀ e ∈ G', a ∉ e := by
    intro e he ha
    have : e ∈ G'.filter (a ∈ ·) := Finset.mem_filter.mpr ⟨he, ha⟩
    rw [Finset.card_eq_zero.mp ha_deg0] at this; simp at this
  -- Strategy: compose σ' with segReverse to make pa and pb adjacent.
  -- Since a has deg 0, boundary at pa is always free.
  -- We arrange so that the smaller position is first.
  -- Obtain min/max positions
  have hpab_ne : pa.val ≠ pb.val := Fin.val_ne_of_ne hpa_ne_pb
  -- Case: already adjacent
  by_cases hadj : pa.val + 1 = pb.val ∨ pb.val + 1 = pa.val ∨
      (pa.val = 0 ∧ pb.val = n - 1) ∨ (pb.val = 0 ∧ pa.val = n - 1)
  · -- Adjacent case: σ' already works
    refine ⟨σ', fun e he => ?_⟩
    rcases Finset.mem_insert.mp he with rfl | hG'
    · rw [mk_mem_relabelEdges_iff]
      change Sym2.mk (pa, pb) ∈ canonEdges n (by omega)
      rcases hadj with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := canonEdges_step_mem hn pa.val (by omega)
        rwa [show (⟨pa.val, by omega⟩ : Fin n) = pa from rfl,
             show (⟨pa.val + 1, by omega⟩ : Fin n) = pb from Fin.ext (by omega)] at this
      · rw [Sym2.eq_swap]
        have := canonEdges_step_mem hn pb.val (by omega)
        rwa [show (⟨pb.val, by omega⟩ : Fin n) = pb from rfl,
             show (⟨pb.val + 1, by omega⟩ : Fin n) = pa from Fin.ext (by omega)] at this
      · rw [Sym2.eq_swap]
        have := canonEdges_wrap_mem hn
        rwa [show (⟨n - 1, by omega⟩ : Fin n) = pb from Fin.ext (by simp [Fin.val_mk]; omega),
             show (⟨0, by omega⟩ : Fin n) = pa from Fin.ext (by simp [Fin.val_mk]; omega)] at this
      · have := canonEdges_wrap_mem hn
        rwa [show (⟨n - 1, by omega⟩ : Fin n) = pa from Fin.ext (by simp [Fin.val_mk]; omega),
             show (⟨0, by omega⟩ : Fin n) = pb from Fin.ext (by simp [Fin.val_mk]; omega)] at this
    · exact hσ' hG'
  · -- Non-adjacent case: use segReverse
    push_neg at hadj
    have h_symm : ∀ (seg : Equiv.Perm (Fin n)), seg.symm = seg →
        ∀ x, (σ' * seg).symm x = seg (σ'.symm x) := by
      intro seg hseg x
      have hinv : seg (seg (σ'.symm x)) = σ'.symm x := by
        have := seg.symm_apply_apply (σ'.symm x); rwa [hseg] at this
      exact (σ' * seg).symm_apply_eq.mpr (by
        rw [Equiv.Perm.mul_apply, hinv, Equiv.apply_symm_apply])
    set np : Fin n := ⟨(pb.val + 1) % n, Nat.mod_lt _ (by omega)⟩ with hnp_def
    have σ'_pa_eq : σ' pa = a := Equiv.apply_symm_apply σ' a
    have σ'_pb_eq : σ' pb = b := Equiv.apply_symm_apply σ' b
    have transfer : ∀ (x u v : Fin n),
        σ'.symm x ∈ Sym2.mk (σ'.symm u, σ'.symm v) → x ∈ Sym2.mk (u, v) := by
      intro x u v hm
      rcases Sym2.mem_iff.mp hm with h | h
      · exact Sym2.mem_iff.mpr (Or.inl (σ'.symm.injective h))
      · exact Sym2.mem_iff.mpr (Or.inr (σ'.symm.injective h))
    have b_unique : ∀ e1 e2 : Edge n,
        e1 ∈ G' → e2 ∈ G' → b ∈ e1 → b ∈ e2 → e1 = e2 := by
      intro e1 e2 h1 h2 hb1 hb2
      by_contra hne
      have hf1 : e1 ∈ G'.filter (fun e => b ∈ e) := Finset.mem_filter.mpr ⟨h1, hb1⟩
      have hf2 : e2 ∈ G'.filter (fun e => b ∈ e) := Finset.mem_filter.mpr ⟨h2, hb2⟩
      have := Finset.one_lt_card.mpr ⟨e1, hf1, e2, hf2, hne⟩
      omega
    rcases Nat.lt_or_gt_of_ne hpab_ne with hlt | hgt
    · have hgap : pa.val + 2 ≤ pb.val := by omega
      by_cases hblock : Sym2.mk (b, σ' np) ∈ G'
      · have hpb_pos : 0 < pb.val := by omega
        have hpa_le_pb1 : pa.val ≤ pb.val - 1 := by omega
        have hpb1_lt : pb.val - 1 < n := by omega
        have hpb1_lt_pb : pb.val - 1 < pb.val := by omega
        have hpb1_step : pb.val - 1 + 1 < n := by omega
        have hpb_eq : pb = ⟨pb.val - 1 + 1, by omega⟩ :=
          Fin.ext (by simp [Fin.val_mk]; omega)
        set seg := segReverse n pa.val (pb.val - 1) hpa_le_pb1 hpb1_lt
        have hseg_symm := segReverse_symm_eq pa.val (pb.val - 1) hpa_le_pb1 hpb1_lt
        refine ⟨σ' * seg, fun e he => ?_⟩
        rcases Finset.mem_insert.mp he with rfl | hG'
        · rw [mk_mem_relabelEdges_iff, h_symm _ hseg_symm, h_symm _ hseg_symm]
          rw [segReverse_inside pa.val (pb.val - 1) hpa_le_pb1 hpb1_lt pa
                (le_refl _) hpa_le_pb1]
          rw [segReverse_outside pa.val (pb.val - 1) hpa_le_pb1 hpb1_lt pb
                (Or.inr hpb1_lt_pb)]
          have hfin1 : (⟨pa.val + (pb.val - 1) - pa.val, by omega⟩ : Fin n) =
              (⟨pb.val - 1, hpb1_lt⟩ : Fin n) := Fin.ext (by simp [Fin.val_mk])
          rw [hfin1, Sym2.eq_swap]
          have hstep_eq : Sym2.mk (pb, (⟨pb.val - 1, hpb1_lt⟩ : Fin n)) =
              Sym2.mk ((⟨pb.val - 1, hpb1_lt⟩ : Fin n),
                ⟨pb.val - 1 + 1, hpb1_step⟩) := by
            rw [Sym2.mk_eq_mk_iff]; right; exact Prod.ext_iff.mpr ⟨hpb_eq, rfl⟩
          rw [hstep_eq]
          exact canonEdges_step_mem hn (pb.val - 1) hpb1_step
        · have he' := hσ' hG'
          induction e using Sym2.ind with
          | h u v =>
            rw [mk_mem_relabelEdges_iff] at he' ⊢
            rw [h_symm _ hseg_symm, h_symm _ hseg_symm]
            set pu := σ'.symm u; set pv := σ'.symm v
            rcases canonEdges_mem_cases hn pu pv he' with ⟨k, hk, hstep⟩ | hwrap
            · have hmapped : Sym2.mk (seg pu, seg pv) =
                  Sym2.mk (seg ⟨k, by omega⟩, seg ⟨k + 1, hk⟩) :=
                congr_arg (Sym2.map seg) hstep
              rw [hmapped]
              by_cases hin : pa.val ≤ k ∧ k + 1 ≤ pb.val - 1
              · exact segReverse_preserves_canon_inside hn _ _
                  hpa_le_pb1 hpb1_lt k hk hin.1 hin.2
              · by_cases hout : k + 1 < pa.val ∨ pb.val - 1 < k
                · exact segReverse_preserves_canon_outside hn _ _
                    hpa_le_pb1 hpb1_lt k hk hout
                · exfalso
                  push_neg at hin hout
                  have hk_bd : k = pa.val - 1 ∨ k = pb.val - 1 := by omega
                  rcases hk_bd with rfl | rfl
                  · have hpa1_pos : 1 ≤ pa.val := by omega
                    have : pa ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; simp [Sym2.mem_iff]
                      right; exact Fin.ext (by simp [Fin.val_mk]; omega)
                    exact ha_free _ hG' (transfer a u v this)
                  · have hpb_mem : pb ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; simp [Sym2.mem_iff]
                      right; exact Fin.ext (by simp [Fin.val_mk]; omega)
                    have hb_uv : b ∈ Sym2.mk (u, v) := transfer b u v hpb_mem
                    have : Sym2.mk (u, v) = Sym2.mk (b, σ' np) :=
                      b_unique _ _ hG' hblock hb_uv
                        (Sym2.mem_iff.mpr (Or.inl rfl))
                    have hother : σ' ⟨pb.val - 1, hpb1_lt⟩ ∈ Sym2.mk (u, v) := by
                      have : ⟨pb.val - 1, hpb1_lt⟩ ∈ Sym2.mk (pu, pv) := by
                        rw [hstep]; exact Sym2.mem_iff.mpr (Or.inl rfl)
                      exact transfer (σ' ⟨pb.val - 1, hpb1_lt⟩) u v (by
                        rwa [Equiv.symm_apply_apply])
                    rw [this] at hother
                    rcases Sym2.mem_iff.mp hother with h | h
                    · rw [← σ'_pb_eq] at h
                      have := Fin.val_eq_of_eq (σ'.injective h)
                      simp [Fin.val_mk] at this; omega
                    · have hval : (⟨pb.val - 1, hpb1_lt⟩ : Fin n) = np :=
                        σ'.injective h
                      have hveq : pb.val - 1 = np.val :=
                        Fin.val_eq_of_eq hval
                      rw [hnp_def] at hveq; simp [Fin.val_mk] at hveq
                      rcases Nat.lt_or_ge (pb.val + 1) n with hlt_n | hge_n
                      · rw [Nat.mod_eq_of_lt hlt_n] at hveq; omega
                      · have : pb.val + 1 = n := by omega
                        rw [this, Nat.mod_self] at hveq; omega
            · have hmapped : Sym2.mk (seg pu, seg pv) =
                  Sym2.mk (seg ⟨n - 1, by omega⟩, seg ⟨0, by omega⟩) :=
                congr_arg (Sym2.map seg) hwrap
              rw [hmapped]
              have hn1_out : (⟨n - 1, by omega⟩ : Fin n).val < pa.val ∨
                  pb.val - 1 < (⟨n - 1, by omega⟩ : Fin n).val := by
                right; simp [Fin.val_mk]; omega
              rw [segReverse_outside pa.val (pb.val - 1) hpa_le_pb1 hpb1_lt
                    ⟨n - 1, by omega⟩ hn1_out]
              by_cases hpa0 : pa.val = 0
              · exfalso
                have hpa_mem : pa ∈ Sym2.mk (pu, pv) := by
                  rw [hwrap]; simp [Sym2.mem_iff]
                  right; exact Fin.ext (by simp [Fin.val_mk]; omega)
                exact ha_free _ hG' (transfer a u v hpa_mem)
              · rw [segReverse_outside pa.val (pb.val - 1) hpa_le_pb1 hpb1_lt
                      ⟨0, by omega⟩ (Or.inl (by simp [Fin.val_mk]; omega))]
                exact canonEdges_wrap_mem hn
      · refine ⟨σ' * segReverse n (pa.val + 1) pb.val (by omega) pb.isLt,
          fun e he => ?_⟩
        have hseg_symm := segReverse_symm_eq (pa.val + 1) pb.val (by omega : pa.val + 1 ≤ pb.val) pb.isLt
        rcases Finset.mem_insert.mp he with rfl | hG'
        · rw [mk_mem_relabelEdges_iff, h_symm _ hseg_symm, h_symm _ hseg_symm]
          rw [segReverse_outside (pa.val + 1) pb.val (by omega) pb.isLt pa
                (Or.inl (by omega))]
          rw [segReverse_inside (pa.val + 1) pb.val (by omega) pb.isLt pb
                (by omega) (le_refl _)]
          have hfin1 : (⟨pa.val + 1 + pb.val - pb.val, by omega⟩ : Fin n) =
              (⟨pa.val + 1, by omega⟩ : Fin n) := Fin.ext (by simp [Fin.val_mk])
          rw [hfin1]
          exact canonEdges_step_mem hn pa.val (by omega)
        · have he' := hσ' hG'
          induction e using Sym2.ind with
          | h u v =>
            rw [mk_mem_relabelEdges_iff] at he' ⊢
            rw [h_symm _ hseg_symm, h_symm _ hseg_symm]
            set seg := segReverse n (pa.val + 1) pb.val (by omega) pb.isLt
            set pu := σ'.symm u; set pv := σ'.symm v
            rcases canonEdges_mem_cases hn pu pv he' with ⟨k, hk, hstep⟩ | hwrap
            · have hmapped : Sym2.mk (seg pu, seg pv) =
                  Sym2.mk (seg ⟨k, by omega⟩, seg ⟨k + 1, hk⟩) :=
                congr_arg (Sym2.map seg) hstep
              rw [hmapped]
              by_cases hin : pa.val + 1 ≤ k ∧ k + 1 ≤ pb.val
              · exact segReverse_preserves_canon_inside hn _ _ (by omega) pb.isLt k hk hin.1 hin.2
              · by_cases hout : k + 1 < pa.val + 1 ∨ pb.val < k
                · exact segReverse_preserves_canon_outside hn _ _ (by omega) pb.isLt k hk hout
                · exfalso
                  push_neg at hin hout
                  have hk_eq : k = pa.val ∨ k = pb.val := by omega
                  rcases hk_eq with rfl | rfl
                  · have : pa ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; exact Sym2.mem_iff.mpr (Or.inl (Fin.ext rfl))
                    exact ha_free _ hG' (transfer a u v this)
                  · have hpb_mem : pb ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; exact Sym2.mem_iff.mpr (Or.inl (Fin.ext rfl))
                    have hb_uv : b ∈ Sym2.mk (u, v) := transfer b u v hpb_mem
                    have hnp_eq : np = ⟨pb.val + 1, hk⟩ := by
                      ext; simp [hnp_def, Nat.mod_eq_of_lt hk]
                    have hnp_mem : ⟨pb.val + 1, hk⟩ ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; exact Sym2.mem_iff.mpr (Or.inr rfl)
                    have hσnp_uv : σ' np ∈ Sym2.mk (u, v) := by
                      rw [hnp_eq]; exact transfer (σ' ⟨pb.val + 1, hk⟩) u v (by
                        rwa [Equiv.symm_apply_apply])
                    have hbnp : b ≠ σ' np := by
                      intro h; rw [← σ'_pb_eq] at h
                      have := σ'.injective h
                      rw [hnp_eq] at this
                      exact absurd (Fin.val_eq_of_eq this) (by simp [Fin.val_mk])
                    have : Sym2.mk (u, v) = Sym2.mk (b, σ' np) := by
                      rcases Sym2.mem_iff.mp hb_uv with rfl | rfl <;>
                        rcases Sym2.mem_iff.mp hσnp_uv with h | h
                      · exact absurd h (Ne.symm hbnp)
                      · rw [h]
                      · rw [h, Sym2.eq_swap]
                      · exact absurd h.symm hbnp
                    rw [this] at hG'; exact hblock hG'
            · have hmapped : Sym2.mk (seg pu, seg pv) =
                  Sym2.mk (seg ⟨n - 1, by omega⟩, seg ⟨0, by omega⟩) :=
                congr_arg (Sym2.map seg) hwrap
              rw [hmapped]
              rw [segReverse_outside (pa.val + 1) pb.val (by omega) pb.isLt
                    ⟨0, by omega⟩ (Or.inl (by simp [Fin.val_mk]))]
              by_cases hpb_n1 : pb.val = n - 1
              · exfalso
                have hpb_mem : pb ∈ Sym2.mk (pu, pv) := by
                  rw [hwrap]; exact Sym2.mem_iff.mpr
                    (Or.inl (Fin.ext (by simp [Fin.val_mk]; omega)))
                have hb_uv : b ∈ Sym2.mk (u, v) := transfer b u v hpb_mem
                have hnp_eq : np = ⟨0, by omega⟩ := by
                  ext; simp [hnp_def, Fin.val_mk, hpb_n1]
                  exact Nat.mod_eq_zero_of_dvd ⟨1, by omega⟩
                have hnp_mem : np ∈ Sym2.mk (pu, pv) := by
                  rw [hwrap, hnp_eq]; exact Sym2.mem_iff.mpr (Or.inr rfl)
                have hσnp_uv : σ' np ∈ Sym2.mk (u, v) :=
                  transfer (σ' np) u v (by rwa [Equiv.symm_apply_apply])
                have hbnp : b ≠ σ' np := by
                  intro h; rw [← σ'_pb_eq] at h
                  have := σ'.injective h
                  rw [hnp_eq] at this
                  exact absurd (Fin.val_eq_of_eq this) (by simp [Fin.val_mk]; omega)
                have : Sym2.mk (u, v) = Sym2.mk (b, σ' np) := by
                  rcases Sym2.mem_iff.mp hb_uv with rfl | rfl <;>
                    rcases Sym2.mem_iff.mp hσnp_uv with h | h
                  · exact absurd h (Ne.symm hbnp)
                  · rw [h]
                  · rw [h, Sym2.eq_swap]
                  · exact absurd h.symm hbnp
                rw [this] at hG'; exact hblock hG'
              · rw [segReverse_outside (pa.val + 1) pb.val (by omega) pb.isLt
                      ⟨n - 1, by omega⟩ (Or.inr (by simp [Fin.val_mk]; omega))]
                exact canonEdges_wrap_mem hn
    · have hgap : pb.val + 2 ≤ pa.val := by omega
      by_cases hblock : Sym2.mk (b, σ' np) ∈ G'
      · have hpa_pos : 0 < pa.val := by omega
        have hpb_le_pa1 : pb.val ≤ pa.val - 1 := by omega
        have hpa1_lt : pa.val - 1 < n := by omega
        have hpa1_lt_pa : pa.val - 1 < pa.val := by omega
        have hpa1_step : pa.val - 1 + 1 < n := by omega
        have hpa_eq : pa = ⟨pa.val - 1 + 1, by omega⟩ :=
          Fin.ext (by simp [Fin.val_mk]; omega)
        set seg := segReverse n pb.val (pa.val - 1) hpb_le_pa1 hpa1_lt
        have hseg_symm := segReverse_symm_eq pb.val (pa.val - 1) hpb_le_pa1 hpa1_lt
        refine ⟨σ' * seg, fun e he => ?_⟩
        rcases Finset.mem_insert.mp he with rfl | hG'
        · rw [mk_mem_relabelEdges_iff, h_symm _ hseg_symm, h_symm _ hseg_symm]
          rw [segReverse_inside pb.val (pa.val - 1) hpb_le_pa1 hpa1_lt pb
                (le_refl _) hpb_le_pa1]
          rw [segReverse_outside pb.val (pa.val - 1) hpb_le_pa1 hpa1_lt pa
                (Or.inr hpa1_lt_pa)]
          have hfin1 : (⟨pb.val + (pa.val - 1) - pb.val, by omega⟩ : Fin n) =
              (⟨pa.val - 1, hpa1_lt⟩ : Fin n) := Fin.ext (by simp [Fin.val_mk])
          rw [hfin1, Sym2.eq_swap]
          have hstep_eq : Sym2.mk ((⟨pa.val - 1, hpa1_lt⟩ : Fin n), pa) =
              Sym2.mk ((⟨pa.val - 1, hpa1_lt⟩ : Fin n),
                ⟨pa.val - 1 + 1, hpa1_step⟩) := by
            congr 1; exact Prod.ext rfl hpa_eq
          rw [hstep_eq]
          exact canonEdges_step_mem hn (pa.val - 1) hpa1_step
        · have he' := hσ' hG'
          induction e using Sym2.ind with
          | h u v =>
            rw [mk_mem_relabelEdges_iff] at he' ⊢
            rw [h_symm _ hseg_symm, h_symm _ hseg_symm]
            set pu := σ'.symm u; set pv := σ'.symm v
            rcases canonEdges_mem_cases hn pu pv he' with ⟨k, hk, hstep⟩ | hwrap
            · have hmapped : Sym2.mk (seg pu, seg pv) =
                  Sym2.mk (seg ⟨k, by omega⟩, seg ⟨k + 1, hk⟩) :=
                congr_arg (Sym2.map seg) hstep
              rw [hmapped]
              by_cases hin : pb.val ≤ k ∧ k + 1 ≤ pa.val - 1
              · exact segReverse_preserves_canon_inside hn _ _
                  hpb_le_pa1 hpa1_lt k hk hin.1 hin.2
              · by_cases hout : k + 1 < pb.val ∨ pa.val - 1 < k
                · exact segReverse_preserves_canon_outside hn _ _
                    hpb_le_pa1 hpa1_lt k hk hout
                · exfalso
                  push_neg at hin hout
                  have hk_bd : k = pb.val - 1 ∨ k = pa.val - 1 := by omega
                  rcases hk_bd with rfl | rfl
                  · have hpb_mem : pb ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; simp [Sym2.mem_iff]
                      right; exact Fin.ext (by simp [Fin.val_mk]; omega)
                    have hb_uv : b ∈ Sym2.mk (u, v) := transfer b u v hpb_mem
                    have : Sym2.mk (u, v) = Sym2.mk (b, σ' np) :=
                      b_unique _ _ hG' hblock hb_uv
                        (Sym2.mem_iff.mpr (Or.inl rfl))
                    have hother : σ' ⟨pb.val - 1, by omega⟩ ∈ Sym2.mk (u, v) := by
                      have : (⟨pb.val - 1, by omega⟩ : Fin n) ∈ Sym2.mk (pu, pv) := by
                        rw [hstep]; exact Sym2.mem_iff.mpr (Or.inl rfl)
                      exact transfer (σ' ⟨pb.val - 1, by omega⟩) u v (by
                        rwa [Equiv.symm_apply_apply])
                    rw [this] at hother
                    rcases Sym2.mem_iff.mp hother with h | h
                    · have heq : (⟨pb.val - 1, by omega⟩ : Fin n) = pb :=
                        σ'.injective (h.trans σ'_pb_eq.symm)
                      exact absurd (Fin.val_eq_of_eq heq)
                        (by simp [Fin.val_mk]; omega)
                    · have hval : (⟨pb.val - 1, by omega⟩ : Fin n) = np :=
                        σ'.injective h
                      have hveq : pb.val - 1 = np.val :=
                        Fin.val_eq_of_eq hval
                      rw [hnp_def] at hveq; simp [Fin.val_mk] at hveq
                      rcases Nat.lt_or_ge (pb.val + 1) n with hlt_n | hge_n
                      · rw [Nat.mod_eq_of_lt hlt_n] at hveq; omega
                      · have : pb.val + 1 = n := by omega
                        rw [this, Nat.mod_self] at hveq; omega
                  · have hpa1_pos : 1 ≤ pa.val := by omega
                    have : pa ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; simp [Sym2.mem_iff]
                      right; exact Fin.ext (by simp [Fin.val_mk]; omega)
                    exact ha_free _ hG' (transfer a u v this)
            · have hmapped : Sym2.mk (seg pu, seg pv) =
                  Sym2.mk (seg ⟨n - 1, by omega⟩, seg ⟨0, by omega⟩) :=
                congr_arg (Sym2.map seg) hwrap
              rw [hmapped]
              have hn1_out : (⟨n - 1, by omega⟩ : Fin n).val < pb.val ∨
                  pa.val - 1 < (⟨n - 1, by omega⟩ : Fin n).val := by
                right; simp [Fin.val_mk]; omega
              rw [segReverse_outside pb.val (pa.val - 1) hpb_le_pa1 hpa1_lt
                    ⟨n - 1, by omega⟩ hn1_out]
              by_cases hpb0 : pb.val = 0
              · exfalso
                have hpb_mem : pb ∈ Sym2.mk (pu, pv) := by
                  rw [hwrap]; simp [Sym2.mem_iff]
                  right; exact Fin.ext (by simp [Fin.val_mk]; omega)
                have hb_uv : b ∈ Sym2.mk (u, v) := transfer b u v hpb_mem
                have : Sym2.mk (u, v) = Sym2.mk (b, σ' np) :=
                  b_unique _ _ hG' hblock hb_uv
                    (Sym2.mem_iff.mpr (Or.inl rfl))
                have hn1_mem : σ' ⟨n - 1, by omega⟩ ∈ Sym2.mk (u, v) := by
                  have : (⟨n - 1, by omega⟩ : Fin n) ∈ Sym2.mk (pu, pv) := by
                    rw [hwrap]; exact Sym2.mem_iff.mpr (Or.inl rfl)
                  exact transfer (σ' ⟨n - 1, by omega⟩) u v (by
                    rwa [Equiv.symm_apply_apply])
                rw [this] at hn1_mem
                rcases Sym2.mem_iff.mp hn1_mem with h | h
                · have heq : (⟨n - 1, by omega⟩ : Fin n) = pb :=
                    σ'.injective (h.trans σ'_pb_eq.symm)
                  exact absurd (Fin.val_eq_of_eq heq)
                    (by simp [Fin.val_mk]; omega)
                · have hval : (⟨n - 1, by omega⟩ : Fin n) = np :=
                    σ'.injective h
                  have hveq : n - 1 = np.val :=
                    Fin.val_eq_of_eq hval
                  rw [hnp_def] at hveq; simp [Fin.val_mk] at hveq
                  have h1_mod : (pb.val + 1) % n = 1 := by
                    rw [hpb0]; simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
                  rw [h1_mod] at hveq; omega
              · rw [segReverse_outside pb.val (pa.val - 1) hpb_le_pa1 hpa1_lt
                      ⟨0, by omega⟩ (Or.inl (by simp [Fin.val_mk]; omega))]
                exact canonEdges_wrap_mem hn
      · refine ⟨σ' * segReverse n (pb.val + 1) pa.val (by omega) pa.isLt,
          fun e he => ?_⟩
        have hseg_symm := segReverse_symm_eq (pb.val + 1) pa.val (by omega : pb.val + 1 ≤ pa.val) pa.isLt
        rcases Finset.mem_insert.mp he with rfl | hG'
        · rw [mk_mem_relabelEdges_iff, h_symm _ hseg_symm, h_symm _ hseg_symm]
          rw [segReverse_outside (pb.val + 1) pa.val (by omega) pa.isLt pb
                (Or.inl (by omega))]
          rw [segReverse_inside (pb.val + 1) pa.val (by omega) pa.isLt pa
                (by omega) (le_refl _)]
          have hfin1 : (⟨pb.val + 1 + pa.val - pa.val, by omega⟩ : Fin n) =
              (⟨pb.val + 1, by omega⟩ : Fin n) := Fin.ext (by simp [Fin.val_mk])
          rw [hfin1, Sym2.eq_swap]
          exact canonEdges_step_mem hn pb.val (by omega)
        · have he' := hσ' hG'
          induction e using Sym2.ind with
          | h u v =>
            rw [mk_mem_relabelEdges_iff] at he' ⊢
            rw [h_symm _ hseg_symm, h_symm _ hseg_symm]
            set seg := segReverse n (pb.val + 1) pa.val (by omega) pa.isLt
            set pu := σ'.symm u; set pv := σ'.symm v
            rcases canonEdges_mem_cases hn pu pv he' with ⟨k, hk, hstep⟩ | hwrap
            · have hmapped : Sym2.mk (seg pu, seg pv) =
                  Sym2.mk (seg ⟨k, by omega⟩, seg ⟨k + 1, hk⟩) :=
                congr_arg (Sym2.map seg) hstep
              rw [hmapped]
              by_cases hin : pb.val + 1 ≤ k ∧ k + 1 ≤ pa.val
              · exact segReverse_preserves_canon_inside hn _ _ (by omega) pa.isLt k hk hin.1 hin.2
              · by_cases hout : k + 1 < pb.val + 1 ∨ pa.val < k
                · exact segReverse_preserves_canon_outside hn _ _ (by omega) pa.isLt k hk hout
                · exfalso
                  push_neg at hin hout
                  have hk_eq : k = pb.val ∨ k = pa.val := by omega
                  rcases hk_eq with rfl | rfl
                  · have hpb_mem : pb ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; exact Sym2.mem_iff.mpr (Or.inl (Fin.ext rfl))
                    have hb_uv : b ∈ Sym2.mk (u, v) := transfer b u v hpb_mem
                    have hnp_eq : np = ⟨pb.val + 1, hk⟩ := by
                      ext; simp [hnp_def, Nat.mod_eq_of_lt hk]
                    have hnp_mem : ⟨pb.val + 1, hk⟩ ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; exact Sym2.mem_iff.mpr (Or.inr rfl)
                    have hσnp_uv : σ' np ∈ Sym2.mk (u, v) := by
                      rw [hnp_eq]; exact transfer (σ' ⟨pb.val + 1, hk⟩) u v (by
                        rwa [Equiv.symm_apply_apply])
                    have hbnp : b ≠ σ' np := by
                      intro h; rw [← σ'_pb_eq] at h
                      have := σ'.injective h
                      rw [hnp_eq] at this
                      exact absurd (Fin.val_eq_of_eq this) (by simp [Fin.val_mk])
                    have : Sym2.mk (u, v) = Sym2.mk (b, σ' np) := by
                      rcases Sym2.mem_iff.mp hb_uv with rfl | rfl <;>
                        rcases Sym2.mem_iff.mp hσnp_uv with h | h
                      · exact absurd h (Ne.symm hbnp)
                      · rw [h]
                      · rw [h, Sym2.eq_swap]
                      · exact absurd h.symm hbnp
                    rw [this] at hG'; exact hblock hG'
                  · have : pa ∈ Sym2.mk (pu, pv) := by
                      rw [hstep]; exact Sym2.mem_iff.mpr (Or.inl (Fin.ext rfl))
                    exact ha_free _ hG' (transfer a u v this)
            · have hmapped : Sym2.mk (seg pu, seg pv) =
                  Sym2.mk (seg ⟨n - 1, by omega⟩, seg ⟨0, by omega⟩) :=
                congr_arg (Sym2.map seg) hwrap
              rw [hmapped]
              rw [segReverse_outside (pb.val + 1) pa.val (by omega) pa.isLt
                    ⟨0, by omega⟩ (Or.inl (by simp [Fin.val_mk]))]
              by_cases hpa_n1 : pa.val = n - 1
              · exfalso
                have hpa_mem : pa ∈ Sym2.mk (pu, pv) := by
                  rw [hwrap]; exact Sym2.mem_iff.mpr
                    (Or.inl (Fin.ext (by simp [Fin.val_mk]; omega)))
                exact ha_free _ hG' (transfer a u v hpa_mem)
              · rw [segReverse_outside (pb.val + 1) pa.val (by omega) pa.isLt
                      ⟨n - 1, by omega⟩ (Or.inr (by simp [Fin.val_mk]; omega))]
                exact canonEdges_wrap_mem hn

open Classical in
theorem pathForest_realizable (hn : n ≥ 4)
    (F : Finset (Edge n))
    (hnoloops : ∀ e ∈ F, ¬ e.IsDiag)
    (hmaxdeg : ∀ v : Fin n, (F.filter fun e => v ∈ e).card ≤ 2)
    (hacyclic : ∀ comp : Finset (Edge n), comp ⊆ F →
      IsIncidentConnected n comp →
      comp.Nonempty →
      comp.card < (incidentVertices comp).card)
    (hcard : F.card < n) :
    ∃ σ : Equiv.Perm (Fin n),
      F ⊆ relabelEdges σ (canonEdges n (by omega)) := by
  suffices key : ∀ k, ∀ G : Finset (Edge n), G.card = k →
      (∀ e ∈ G, ¬ e.IsDiag) →
      (∀ v : Fin n, (G.filter fun e => v ∈ e).card ≤ 2) →
      (∀ comp : Finset (Edge n), comp ⊆ G →
        IsIncidentConnected n comp → comp.Nonempty →
        comp.card < (incidentVertices comp).card) →
      G.card < n →
      ∃ σ : Equiv.Perm (Fin n),
        G ⊆ relabelEdges σ (canonEdges n (by omega)) from
    key F.card F rfl hnoloops hmaxdeg hacyclic hcard
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro G hGk hnoloops' hmaxdeg' hacyclic' hcard'
    by_cases hG0 : G.card = 0
    · exact ⟨Equiv.refl _, by simp [Finset.card_eq_zero.mp hG0]⟩
    · have hGne : G.Nonempty := Finset.nonempty_of_ne_empty (by intro h; exact hG0 (Finset.card_eq_zero.mpr h))
      obtain ⟨e0, he0⟩ := hGne
      obtain ⟨u0, hu0_mem⟩ : ∃ u0 : Fin n, u0 ∈ e0 := by
        induction e0 using Sym2.ind with | h a b => exact ⟨a, Sym2.mem_mk_left a b⟩
      have hu0 : ∃ e ∈ G, u0 ∈ e := ⟨e0, he0, hu0_mem⟩
      let comp := edgeComponentOf n G u0
      have hcomp_sub := edgeComponentOf_sub n G u0
      have hcomp_conn := edgeComponentOf_incident_connected n G u0 hu0
      have hcomp_ne := edgeComponentOf_nonempty n G u0 hu0
      have hcomp_noloops : ∀ e ∈ comp, ¬ e.IsDiag := fun e he => hnoloops' e (hcomp_sub he)
      have hdeg_le2 : ∀ v : Fin n, vertexDegreeIn n comp v ≤ 2 :=
        fun v => le_trans (edgeComponentOf_degree_le n G u0 v) (hmaxdeg' v)
      have hcomp_acyc := hacyclic' comp hcomp_sub hcomp_conn hcomp_ne
      have hnotcyc : ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) := by
        intro hall
        have hsum := sum_vertexDegrees_eq_twice_card n comp hcomp_noloops
        have hinc_eq : (incidentVertices comp).card =
            (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 2).card := by
          congr 1; ext v; simp only [incidentVertices, Finset.mem_filter,
            Finset.mem_univ, true_and]
          unfold vertexDegreeIn
          constructor
          · intro hpos
            rcases hall v with h0 | h2
            · unfold vertexDegreeIn at h0; omega
            · unfold vertexDegreeIn at h2; exact h2
          · intro h2; omega
        have hsum_eq : ∑ v : Fin n, vertexDegreeIn n comp v =
            2 * (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 2).card := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun v => vertexDegreeIn n comp v = 2)]
          have h1 : ∑ v ∈ Finset.univ.filter (fun v => vertexDegreeIn n comp v = 2),
              vertexDegreeIn n comp v =
            2 * (Finset.univ.filter (fun v => vertexDegreeIn n comp v = 2)).card := by
            rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)]
            simp [Finset.sum_const, mul_comm]
          have h2 : ∑ v ∈ Finset.univ.filter (fun v => ¬(vertexDegreeIn n comp v = 2)),
              vertexDegreeIn n comp v = 0 := by
            apply Finset.sum_eq_zero
            intro v hv
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
            rcases hall v with h0 | h2e
            · exact h0
            · exact absurd h2e hv
          omega
        omega
      -- Extract a degree-1 vertex from the non-cycle component
      push_neg at hnotcyc
      obtain ⟨v1, hv1_not02⟩ := hnotcyc
      have hv1_deg1 : vertexDegreeIn n comp v1 = 1 := by
        have := hdeg_le2 v1; omega
      -- v1's unique edge in comp (and in G, since comp is a component)
      have hv1_card : (comp.filter fun e => v1 ∈ e).card = 1 := hv1_deg1
      obtain ⟨ev, hev_mem_filt⟩ := Finset.card_pos.mp (by omega :
        0 < (comp.filter fun e => v1 ∈ e).card)
      have hev_in_comp : ev ∈ comp := (Finset.mem_filter.mp hev_mem_filt).1
      have hv1_in_ev : v1 ∈ ev := (Finset.mem_filter.mp hev_mem_filt).2
      have hev_in_G : ev ∈ G := hcomp_sub hev_in_comp
      -- Get both endpoints
      obtain ⟨a, b, hab_eq⟩ : ∃ a b : Fin n, ev = Sym2.mk (a, b) := by
        induction ev using Sym2.ind with | h x y => exact ⟨x, y, rfl⟩
      have hab_ne : a ≠ b := by
        intro h; exact hnoloops' ev hev_in_G (hab_eq ▸ Sym2.mk_isDiag_iff.mpr h)
      subst hab_eq
      -- WLOG v1 = a (or swap to make v1 the first endpoint)
      have hv1_ab : v1 = a ∨ v1 = b := by
        rcases Sym2.mem_iff.mp hv1_in_ev with h | h <;> [left; right] <;> exact h
      -- Erase ev from G
      let G' := G.erase (Sym2.mk (a, b))
      have hG'_card : G'.card = k - 1 := Finset.card_erase_of_mem hev_in_G ▸ hGk ▸ rfl
      have hG'_noloops : ∀ e ∈ G', ¬ e.IsDiag :=
        fun e he => hnoloops' e (Finset.mem_of_mem_erase he)
      have hG'_maxdeg : ∀ v : Fin n, (G'.filter fun e => v ∈ e).card ≤ 2 :=
        fun v => le_trans (Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.erase_subset _ G))) (hmaxdeg' v)
      have hG'_acyclic : ∀ comp' ⊆ G', IsIncidentConnected n comp' →
          comp'.Nonempty → comp'.card < (incidentVertices comp').card :=
        fun comp' hc hconn hne => hacyclic' comp'
          (Finset.Subset.trans hc (Finset.erase_subset _ G)) hconn hne
      have hG'_lt_n : G'.card < n := by
        have := Finset.card_erase_of_mem hev_in_G; omega
      obtain ⟨σ', hσ'⟩ := ih (k - 1) (by omega) G' hG'_card
        hG'_noloops hG'_maxdeg hG'_acyclic hG'_lt_n
      -- v1 has degree 0 in G' (its only edge in G was ev, which was erased)
      -- Key: component maximality — edges of G incident to v1 are all in comp
      have hv1_degG : vertexDegreeIn n G v1 = 1 := by
        have hv1_reach : (edgeSetToGraph n G).Reachable u0 v1 := by
          change Sym2.mk (a, b) ∈ G.filter _ at hev_in_comp
          simp only [Finset.mem_filter] at hev_in_comp
          obtain ⟨_, w, hw_mem, hw_reach⟩ := hev_in_comp
          by_cases hvw : v1 = w
          · exact hvw ▸ hw_reach
          · have hmem : Sym2.mk (w, v1) ∈ G := by
              rcases Sym2.mem_iff.mp hw_mem with rfl | rfl <;>
                rcases Sym2.mem_iff.mp hv1_in_ev with rfl | rfl
              · exact absurd rfl hvw
              · exact hev_in_G
              · rw [Sym2.eq_swap]; exact hev_in_G
              · exact absurd rfl hvw
            exact hw_reach.trans (SimpleGraph.Adj.reachable ⟨fun h => hvw h.symm, hmem⟩)
        rw [← edgeComponentOf_degree_eq n G u0 v1 hv1_reach]; exact hv1_deg1
      have hv1_deg0_G' : (G'.filter fun e => v1 ∈ e).card = 0 := by
        have hsub : G'.filter (v1 ∈ ·) ⊆ (G.filter (v1 ∈ ·)).erase (Sym2.mk (a, b)) := by
          intro e he
          have ⟨hm, hv⟩ := Finset.mem_filter.mp he
          have ⟨hne, hmG⟩ := Finset.mem_erase.mp hm
          exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨hmG, hv⟩⟩
        have hcard := Finset.card_erase_of_mem
          (Finset.mem_filter.mpr ⟨hev_in_G, hv1_in_ev⟩ :
            Sym2.mk (a, b) ∈ G.filter (v1 ∈ ·))
        have := Finset.card_le_card hsub
        unfold vertexDegreeIn at hv1_degG
        omega
      -- Helper: erasing ev from the filter of G gives a bound
      have hdeg_erase_bound : ∀ w : Fin n, w ∈ Sym2.mk (a, b) →
          (G'.filter fun e => w ∈ e).card ≤ 1 := by
        intro w hw
        have hsub : G'.filter (w ∈ ·) ⊆ (G.filter (w ∈ ·)).erase (Sym2.mk (a, b)) := by
          intro e he
          have ⟨hm, hv⟩ := Finset.mem_filter.mp he
          have ⟨hne, hmG⟩ := Finset.mem_erase.mp hm
          exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨hmG, hv⟩⟩
        have hcard := Finset.card_erase_of_mem
          (Finset.mem_filter.mpr ⟨hev_in_G, hw⟩ :
            Sym2.mk (a, b) ∈ G.filter (w ∈ ·))
        have := Finset.card_le_card hsub
        have := hmaxdeg' w
        omega
      -- Identify which endpoint is the leaf (v1) and call the helper
      -- We need: first arg to helper has deg 0, second has deg ≤ 1
      cases hv1_ab with
      | inl hv1a =>
        -- v1 = a: a has deg 0 in G'
        obtain ⟨σ, hσ⟩ := subset_relabelEdges_insert_of_deg0 hn G' a b hab_ne σ' hσ'
          (hv1a ▸ hv1_deg0_G') (hdeg_erase_bound b (Sym2.mem_mk_right a b))
        exact ⟨σ, fun e he => by
          by_cases heq : e = Sym2.mk (a, b)
          · exact hσ (heq ▸ Finset.mem_insert_self _ _)
          · exact hσ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨heq, he⟩))⟩
      | inr hv1b =>
        -- v1 = b: b has deg 0 in G'
        obtain ⟨σ, hσ⟩ := subset_relabelEdges_insert_of_deg0 hn G' b a hab_ne.symm σ' hσ'
          (hv1b ▸ hv1_deg0_G') (hdeg_erase_bound a (Sym2.mem_mk_left a b))
        exact ⟨σ, fun e he => by
          by_cases heq : e = Sym2.mk (a, b)
          · rw [heq, Sym2.eq_swap]; exact hσ (Finset.mem_insert_self _ _)
          · have hne : e ≠ Sym2.mk (a, b) := by
              intro h; exact heq (by rw [h, Sym2.eq_swap])
            exact hσ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, he⟩))⟩

theorem pathCompatible_realizable (hn : n ≥ 4)
    (ρ : Restriction n)
    (_hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
    (hcard : ρ.forcedPresent.card < n) :
    ∃ σ : Equiv.Perm (Fin n),
      ρ.forcedPresent ⊆ relabelEdges σ (canonEdges n (by omega)) := by
  rcases hpath with ⟨hdeg, hloops, hacyclic⟩
  exact pathForest_realizable hn ρ.forcedPresent hloops
    (fun v => by
      calc (ρ.forcedPresent.filter fun e => v ∈ e).card
          ≤ Finset.univ.sup (fun w : Fin n =>
              (ρ.forcedPresent.filter fun e => w ∈ e).card) := by
            apply Finset.le_sup (show v ∈ Finset.univ from Finset.mem_univ v)
        _ ≤ 2 := hdeg)
    hacyclic hcard

theorem restrictedHamCycles_forcedPresent_nonempty (hn : n ≥ 4)
    (ρ : Restriction n)
    (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
    (hcard : ρ.forcedPresent.card < n) :
    (restrictedHamCycles n ⟨ρ.forcedPresent, (∅ : Finset (Edge n))⟩).Nonempty := by
  obtain ⟨σ, hσ⟩ := pathCompatible_realizable hn ρ hcons hpath hcard
  exact ⟨_, restrictedHamCycles_mem_of_relabel_forcedPresent hn _ σ hσ⟩

end PathForestRealize

end PNeNp
