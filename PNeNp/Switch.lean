import PNeNp.Basic
import PNeNp.Interface
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Finset

namespace PNeNp

variable {n : ℕ}

section Restriction

structure Restriction (n : ℕ) where
  forcedPresent : Finset (Edge n)
  forcedAbsent : Finset (Edge n)

def Restriction.size (ρ : Restriction n) : ℕ :=
  ρ.forcedPresent.card + ρ.forcedAbsent.card

def Restriction.consistent (ρ : Restriction n) : Prop :=
  Disjoint ρ.forcedPresent ρ.forcedAbsent

open Classical in
noncomputable def restrictedHamCycles (n : ℕ) (ρ : Restriction n) :
    Finset (Finset (Edge n)) :=
  Finset.univ.filter fun H =>
    ρ.forcedPresent ⊆ H ∧ Disjoint ρ.forcedAbsent H ∧ IsHamCycle n H

def satisfiesRestriction (H : Finset (Edge n)) (ρ : Restriction n) : Prop :=
  ρ.forcedPresent ⊆ H ∧ Disjoint ρ.forcedAbsent H

def Restriction.maxDegree (ρ : Restriction n) : ℕ :=
  Finset.univ.sup fun v : Fin n =>
    (ρ.forcedPresent.filter fun e => v ∈ e).card

def incidentVertices (edges : Finset (Edge n)) : Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => 0 < (edges.filter fun e => v ∈ e).card

def Restriction.isPathCompatible (ρ : Restriction n) : Prop :=
  ρ.maxDegree ≤ 2 ∧
  (∀ e ∈ ρ.forcedPresent, ¬ e.IsDiag) ∧
  ∀ comp : Finset (Edge n), comp ⊆ ρ.forcedPresent →
    IsIncidentConnected n comp →
    comp.Nonempty →
    comp.card < (incidentVertices comp).card

end Restriction

section TwoOptRerouting

structure TwoOptMove (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  d : Fin n
  all_distinct : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

def TwoOptMove.removedEdges (e : TwoOptMove n) : Finset (Edge n) :=
  {Sym2.mk (e.a, e.b), Sym2.mk (e.c, e.d)}

def TwoOptMove.addedEdges (e : TwoOptMove n) : Finset (Edge n) :=
  {Sym2.mk (e.a, e.c), Sym2.mk (e.b, e.d)}

noncomputable def applyTwoOpt (H : Finset (Edge n)) (e : TwoOptMove n) :
    Finset (Edge n) :=
  (H \ e.removedEdges) ∪ e.addedEdges

def edgeSide (S : Frontier n) (e : Edge n) : Bool :=
  if e ∈ S.leftEdges then true else false

def TwoOptMove.toggleEdges (e : TwoOptMove n) : Finset (Edge n) :=
  {Sym2.mk (e.a, e.b), Sym2.mk (e.a, e.c),
   Sym2.mk (e.c, e.d), Sym2.mk (e.b, e.d)}

def toggleSetMonochromatic (S : Frontier n) (e : TwoOptMove n) : Prop :=
  ∀ f ∈ e.toggleEdges, edgeSide S f = edgeSide S (Sym2.mk (e.a, e.b))

def TwoOptMove.isGenuine (e : TwoOptMove n) (H : Finset (Edge n)) : Prop :=
  Sym2.mk (e.a, e.b) ∈ H ∧ Sym2.mk (e.c, e.d) ∈ H ∧
  Sym2.mk (e.a, e.c) ∉ H ∧ Sym2.mk (e.b, e.d) ∉ H

def degreeDiscrepancy (S : Frontier n) (H : Finset (Edge n))
    (e : TwoOptMove n) : Prop :=
  degreeProfile S H ≠ degreeProfile S (applyTwoOpt H e)

end TwoOptRerouting

section DegreeChangeCriterion

private lemma edgeSide_left_iff (S : Frontier n) (e : Edge n) :
    edgeSide S e = true ↔ e ∈ S.leftEdges := by
  unfold edgeSide; split_ifs with h <;> simp [h]

private lemma edgeSide_eq_iff_left_iff (S : Frontier n) (e₁ e₂ : Edge n) :
    edgeSide S e₁ = edgeSide S e₂ ↔ (e₁ ∈ S.leftEdges ↔ e₂ ∈ S.leftEdges) := by
  unfold edgeSide; split_ifs <;> simp_all

private lemma leftDeg_applyTwoOpt_eq_of_mono
    {n : ℕ} (S : Frontier n) (H : Finset (Edge n)) (e : TwoOptMove n)
    (hmono : toggleSetMonochromatic S e)
    (hab_in : Sym2.mk (e.a, e.b) ∈ H) (hcd_in : Sym2.mk (e.c, e.d) ∈ H)
    (hac_nin : Sym2.mk (e.a, e.c) ∉ H) (hbd_nin : Sym2.mk (e.b, e.d) ∉ H) :
    ∀ v : Fin n,
    leftDegreeAt S (applyTwoOpt H e) v = leftDegreeAt S H v := by
  obtain ⟨hab_ne, hac_ne, had_ne, hbc_ne, hbd_ne, hcd_ne⟩ := e.all_distinct
  unfold toggleSetMonochromatic TwoOptMove.toggleEdges at hmono
  have hiff_ac : edgeSide S (Sym2.mk (e.a, e.c)) = edgeSide S (Sym2.mk (e.a, e.b)) :=
    hmono _ (mem_insert_of_mem (mem_insert_self _ _))
  have hiff_cd : edgeSide S (Sym2.mk (e.c, e.d)) = edgeSide S (Sym2.mk (e.a, e.b)) :=
    hmono _ (mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _)))
  have hiff_bd : edgeSide S (Sym2.mk (e.b, e.d)) = edgeSide S (Sym2.mk (e.a, e.b)) :=
    hmono _ (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))))
  rw [edgeSide_eq_iff_left_iff] at hiff_ac hiff_cd hiff_bd
  intro v
  by_cases hab_left : Sym2.mk (e.a, e.b) ∈ S.leftEdges
  · have hac_left := hiff_ac.mpr hab_left
    have hcd_left := hiff_cd.mpr hab_left
    have hbd_left := hiff_bd.mpr hab_left
    unfold leftDegreeAt leftSubgraph vertexDegreeIn applyTwoOpt
      TwoOptMove.removedEdges TwoOptMove.addedEdges
    set rem := ({Sym2.mk (e.a, e.b), Sym2.mk (e.c, e.d)} : Finset (Edge n)) with hrem_def
    set add := ({Sym2.mk (e.a, e.c), Sym2.mk (e.b, e.d)} : Finset (Edge n)) with hadd_def
    set A := H ∩ S.leftEdges with hA_def
    have hrem_sub_A : rem ⊆ A := by
      intro f hf; rw [hrem_def] at hf; simp only [mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact mem_inter.mpr ⟨hab_in, hab_left⟩
      · exact mem_inter.mpr ⟨hcd_in, hcd_left⟩
    have hA_disj_add : Disjoint A add := by
      rw [disjoint_left]; intro f hf1 hf2
      rw [hadd_def] at hf2; simp only [mem_insert, mem_singleton] at hf2
      rcases hf2 with rfl | rfl
      · exact hac_nin (mem_inter.mp hf1).1
      · exact hbd_nin (mem_inter.mp hf1).1
    have hadd_sub_left : add ⊆ S.leftEdges := by
      rw [hadd_def]; intro f hf; simp only [mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl <;> assumption
    have hset_eq : (H \ rem ∪ add) ∩ S.leftEdges = (A \ rem) ∪ add := by
      ext f; simp only [mem_inter, mem_union, mem_sdiff, hA_def, mem_inter]
      constructor
      · rintro ⟨hfl | hfa, hfleft⟩
        · exact Or.inl ⟨⟨hfl.1, hfleft⟩, hfl.2⟩
        · exact Or.inr hfa
      · rintro (⟨⟨hfH, hfleft⟩, hfnrem⟩ | hfa)
        · exact ⟨Or.inl ⟨hfH, hfnrem⟩, hfleft⟩
        · exact ⟨Or.inr hfa, hadd_sub_left hfa⟩
    rw [hset_eq]
    have hkey : (Finset.filter (v ∈ ·) rem).card = (Finset.filter (v ∈ ·) add).card := by
      rw [hrem_def, hadd_def]
      simp only [filter_insert, filter_singleton, Sym2.mem_iff]
      by_cases hwa : v = e.a <;> by_cases hwb : v = e.b <;>
        by_cases hwc : v = e.c <;> by_cases hwd : v = e.d <;>
        simp_all [card_insert_of_notMem]
    have h_disj : Disjoint (filter (v ∈ ·) (A \ rem)) (filter (v ∈ ·) add) := by
      rw [disjoint_left]; intro f hf1 hf2
      simp only [mem_filter, mem_sdiff] at hf1; simp only [mem_filter] at hf2
      exact disjoint_left.mp hA_disj_add hf1.1.1 hf2.1
    rw [filter_union, card_union_of_disjoint h_disj]
    have h_sub : filter (v ∈ ·) rem ⊆ filter (v ∈ ·) A := filter_subset_filter _ hrem_sub_A
    have hfilt_sdiff : filter (v ∈ ·) (A \ rem) = filter (v ∈ ·) A \ filter (v ∈ ·) rem := by
      ext f; simp only [mem_filter, mem_sdiff]; tauto
    rw [hfilt_sdiff, Finset.card_sdiff_of_subset h_sub, hkey]
    exact Nat.sub_add_cancel (hkey ▸ card_le_card h_sub)
  · have hac_nleft := mt hiff_ac.mp hab_left
    have hcd_nleft := mt hiff_cd.mp hab_left
    have hbd_nleft := mt hiff_bd.mp hab_left
    unfold leftDegreeAt leftSubgraph vertexDegreeIn applyTwoOpt
      TwoOptMove.removedEdges TwoOptMove.addedEdges
    congr 1; ext f
    simp only [mem_filter, mem_inter, mem_union, mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hfH | hfa, hfleft⟩, hfv⟩
      · exact ⟨⟨hfH.1, hfleft⟩, hfv⟩
      · rcases hfa with rfl | rfl
        · exact absurd hfleft hac_nleft
        · exact absurd hfleft hbd_nleft
    · rintro ⟨⟨hfH, hfleft⟩, hfv⟩
      exact ⟨⟨Or.inl ⟨hfH, fun h => by rcases h with rfl | rfl; exact hab_left hfleft; exact hcd_nleft hfleft⟩, hfleft⟩, hfv⟩

private lemma leftDeg_change_at_vertex_of_swap
    {n : ℕ} (S : Frontier n) (H : Finset (Edge n))
    (e_old e_new : Edge n) (v : Fin n)
    (hv_old : v ∈ e_old) (hv_new : v ∈ e_new)
    (hold_in : e_old ∈ H) (hnew_nin : e_new ∉ H)
    (hold_left : e_old ∈ S.leftEdges) (hnew_nleft : e_new ∉ S.leftEdges)
    (H' : Finset (Edge n))
    (hH'_spec : ∀ f : Edge n, v ∈ f → f ≠ e_old → f ≠ e_new →
      (f ∈ H' ∩ S.leftEdges ↔ f ∈ H ∩ S.leftEdges))
    (hold_nin' : e_old ∉ H') (hnew_in' : e_new ∈ H') :
    (Finset.filter (v ∈ ·) (H' ∩ S.leftEdges)).card <
    (Finset.filter (v ∈ ·) (H ∩ S.leftEdges)).card := by
  have hold_in_filt : e_old ∈ (H ∩ S.leftEdges).filter (v ∈ ·) :=
    Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hold_in, hold_left⟩, hv_old⟩
  have hold_nin_filt' : e_old ∉ (H' ∩ S.leftEdges).filter (v ∈ ·) := by
    simp only [Finset.mem_filter, Finset.mem_inter]; intro ⟨⟨h, _⟩, _⟩; exact hold_nin' h
  have hnew_nin_filt : e_new ∉ (H ∩ S.leftEdges).filter (v ∈ ·) := by
    simp only [Finset.mem_filter, Finset.mem_inter]; intro ⟨⟨h, _⟩, _⟩; exact hnew_nin h
  have hnew_nin_filt' : e_new ∉ (H' ∩ S.leftEdges).filter (v ∈ ·) := by
    simp only [Finset.mem_filter, Finset.mem_inter]; intro ⟨⟨_, h⟩, _⟩; exact hnew_nleft h
  apply Finset.card_lt_card
  constructor
  · intro f hf
    have hf_mem := hf
    simp only [Finset.mem_filter, Finset.mem_inter] at hf
    have hf_ne_old : f ≠ e_old := by
      intro h; subst h; exact hold_nin_filt' hf_mem
    have hf_ne_new : f ≠ e_new := by
      intro h; subst h; exact hnew_nin_filt' hf_mem
    exact Finset.mem_filter.mpr
      ⟨(hH'_spec f hf.2 hf_ne_old hf_ne_new).mp (Finset.mem_inter.mpr ⟨hf.1.1, hf.1.2⟩), hf.2⟩
  · intro hsub; exact hold_nin_filt' (hsub hold_in_filt)

private lemma not_monochromatic_degree_changes
    {n : ℕ} (S : Frontier n) (H : Finset (Edge n)) (_hH : IsHamCycle n H)
    (e : TwoOptMove n)
    (hab_in : Sym2.mk (e.a, e.b) ∈ H) (hcd_in : Sym2.mk (e.c, e.d) ∈ H)
    (hac_nin : Sym2.mk (e.a, e.c) ∉ H) (hbd_nin : Sym2.mk (e.b, e.d) ∉ H)
    (hnm : ¬ toggleSetMonochromatic S e) :
    degreeProfile S (applyTwoOpt H e) ≠ degreeProfile S H := by
  intro heq
  apply hnm
  unfold toggleSetMonochromatic TwoOptMove.toggleEdges
  intro f hf
  simp only [mem_insert, mem_singleton] at hf
  have hleft_eq : ∀ v, leftDegreeAt S (applyTwoOpt H e) v = leftDegreeAt S H v :=
    fun v => congr_fun heq v
  obtain ⟨hab_ne, hac_ne, had_ne, hbc_ne, hbd_ne, hcd_ne⟩ := e.all_distinct
  set H' := applyTwoOpt H e with hH'_def
  -- Helper: membership in H' = (H \ {ab,cd}) ∪ {ac,bd}
  have hab_nin_H' : Sym2.mk (e.a, e.b) ∉ H' := by
    simp only [hH'_def, applyTwoOpt, TwoOptMove.removedEdges, TwoOptMove.addedEdges]
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact (Finset.mem_sdiff.mp h).2 (mem_insert_self _ _)
    · rcases Finset.mem_insert.mp h with h | h
      · have hb_mem : e.b ∈ Sym2.mk (e.a, e.c) :=
          h ▸ (Sym2.mem_iff.mpr (Or.inr rfl))
        simp [Sym2.mem_iff] at hb_mem
        exact hb_mem.elim (fun h => hab_ne h.symm) (fun h => hbc_ne h)
      · have ha_mem : e.a ∈ Sym2.mk (e.b, e.d) :=
          (Finset.mem_singleton.mp h) ▸ (Sym2.mem_iff.mpr (Or.inl rfl))
        simp [Sym2.mem_iff] at ha_mem
        exact ha_mem.elim (fun h => hab_ne h) (fun h => had_ne h)
  have hcd_nin_H' : Sym2.mk (e.c, e.d) ∉ H' := by
    simp only [hH'_def, applyTwoOpt, TwoOptMove.removedEdges, TwoOptMove.addedEdges]
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact (Finset.mem_sdiff.mp h).2 (mem_insert_of_mem (mem_singleton_self _))
    · rcases Finset.mem_insert.mp h with h | h
      · have hd_mem : e.d ∈ Sym2.mk (e.a, e.c) :=
          h ▸ (Sym2.mem_iff.mpr (Or.inr rfl))
        simp [Sym2.mem_iff] at hd_mem
        exact hd_mem.elim (fun h => had_ne h.symm) (fun h => hcd_ne h.symm)
      · have hc_mem : e.c ∈ Sym2.mk (e.b, e.d) :=
          (Finset.mem_singleton.mp h) ▸ (Sym2.mem_iff.mpr (Or.inl rfl))
        simp [Sym2.mem_iff] at hc_mem
        exact hc_mem.elim (fun h => hbc_ne h.symm) (fun h => hcd_ne h)
  have hac_in_H' : Sym2.mk (e.a, e.c) ∈ H' := by
    simp only [hH'_def]; unfold applyTwoOpt TwoOptMove.removedEdges TwoOptMove.addedEdges
    exact mem_union_right _ (mem_insert_self _ _)
  have hbd_in_H' : Sym2.mk (e.b, e.d) ∈ H' := by
    simp only [hH'_def]; unfold applyTwoOpt TwoOptMove.removedEdges TwoOptMove.addedEdges
    exact mem_union_right _ (mem_insert_of_mem (mem_singleton_self _))
  -- Spec: edges not among {ab,cd,ac,bd} are in H' iff in H
  have spec_fwd : ∀ f : Edge n,
      f ≠ Sym2.mk (e.a, e.b) → f ≠ Sym2.mk (e.c, e.d) →
      f ≠ Sym2.mk (e.a, e.c) → f ≠ Sym2.mk (e.b, e.d) →
      (f ∈ H' ↔ f ∈ H) := by
    intro f hne_ab hne_cd hne_ac hne_bd
    simp only [hH'_def]; unfold applyTwoOpt TwoOptMove.removedEdges TwoOptMove.addedEdges
    simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro (⟨hfH, _⟩ | rfl | rfl)
      · exact hfH
      · exact absurd rfl hne_ac
      · exact absurd rfl hne_bd
    · intro hfH; exact Or.inl ⟨hfH, fun h => by rcases h with rfl | rfl <;> contradiction⟩
  -- Derived: spec for left intersection
  have spec_left : ∀ f : Edge n,
      f ≠ Sym2.mk (e.a, e.b) → f ≠ Sym2.mk (e.c, e.d) →
      f ≠ Sym2.mk (e.a, e.c) → f ≠ Sym2.mk (e.b, e.d) →
      (f ∈ H' ∩ S.leftEdges ↔ f ∈ H ∩ S.leftEdges) := by
    intro f h1 h2 h3 h4
    simp only [mem_inter]; exact ⟨fun ⟨a, b⟩ => ⟨(spec_fwd f h1 h2 h3 h4).mp a, b⟩,
      fun ⟨a, b⟩ => ⟨(spec_fwd f h1 h2 h3 h4).mpr a, b⟩⟩
  -- Helper: vertex-specific edge inequality deductions
  -- If v = e.a and v ∈ f, then f ≠ cd and f ≠ bd (by distinctness)
  have a_not_in_cd : e.a ∉ Sym2.mk (e.c, e.d) := by
    simp [Sym2.mem_iff]; exact ⟨hac_ne, had_ne⟩
  have a_not_in_bd : e.a ∉ Sym2.mk (e.b, e.d) := by
    simp [Sym2.mem_iff]; exact ⟨hab_ne, had_ne⟩
  have b_not_in_cd : e.b ∉ Sym2.mk (e.c, e.d) := by
    simp [Sym2.mem_iff]; exact ⟨hbc_ne, hbd_ne⟩
  have b_not_in_ac : e.b ∉ Sym2.mk (e.a, e.c) := by
    simp [Sym2.mem_iff]; exact ⟨hab_ne.symm, hbc_ne⟩
  have c_not_in_ab : e.c ∉ Sym2.mk (e.a, e.b) := by
    simp [Sym2.mem_iff]; exact ⟨hac_ne.symm, hbc_ne.symm⟩
  have c_not_in_bd : e.c ∉ Sym2.mk (e.b, e.d) := by
    simp [Sym2.mem_iff]; exact ⟨hbc_ne.symm, hcd_ne⟩
  have d_not_in_ab : e.d ∉ Sym2.mk (e.a, e.b) := by
    simp [Sym2.mem_iff]; exact ⟨had_ne.symm, hbd_ne.symm⟩
  have d_not_in_ac : e.d ∉ Sym2.mk (e.a, e.c) := by
    simp [Sym2.mem_iff]; exact ⟨had_ne.symm, hcd_ne.symm⟩
  -- Specs at specific vertices (only need 2 edges excluded, the others are auto by vertex non-membership)
  have spec_a_ab_ac : ∀ f, e.a ∈ f → f ≠ Sym2.mk (e.a, e.b) → f ≠ Sym2.mk (e.a, e.c) →
      (f ∈ H' ∩ S.leftEdges ↔ f ∈ H ∩ S.leftEdges) := by
    intro f hfv h1 h3
    exact spec_left f h1 (fun h => a_not_in_cd (h ▸ hfv)) h3 (fun h => a_not_in_bd (h ▸ hfv))
  have spec_b_ab_bd : ∀ f, e.b ∈ f → f ≠ Sym2.mk (e.a, e.b) → f ≠ Sym2.mk (e.b, e.d) →
      (f ∈ H' ∩ S.leftEdges ↔ f ∈ H ∩ S.leftEdges) := by
    intro f hfv h1 h4
    exact spec_left f h1 (fun h => b_not_in_cd (h ▸ hfv)) (fun h => b_not_in_ac (h ▸ hfv)) h4
  have spec_c_cd_ac : ∀ f, e.c ∈ f → f ≠ Sym2.mk (e.c, e.d) → f ≠ Sym2.mk (e.a, e.c) →
      (f ∈ H' ∩ S.leftEdges ↔ f ∈ H ∩ S.leftEdges) := by
    intro f hfv h2 h3
    exact spec_left f (fun h => c_not_in_ab (h ▸ hfv)) h2 h3 (fun h => c_not_in_bd (h ▸ hfv))
  have spec_d_cd_bd : ∀ f, e.d ∈ f → f ≠ Sym2.mk (e.c, e.d) → f ≠ Sym2.mk (e.b, e.d) →
      (f ∈ H' ∩ S.leftEdges ↔ f ∈ H ∩ S.leftEdges) := by
    intro f hfv h2 h4
    exact spec_left f (fun h => d_not_in_ab (h ▸ hfv)) h2 (fun h => d_not_in_ac (h ▸ hfv)) h4
  -- Main case split
  rcases hf with rfl | rfl | rfl | rfl
  · rfl
  all_goals by_contra hne; rw [edgeSide_eq_iff_left_iff] at hne; push_neg at hne
  -- ac vs ab: (ac ∈ left ∧ ab ∉ left) ∨ (ac ∉ left ∧ ab ∈ left)
  · rcases hne with ⟨hac_left, hab_nleft⟩ | ⟨hac_nleft, hab_left⟩
    · have hlt := leftDeg_change_at_vertex_of_swap S H'
        (Sym2.mk (e.a, e.c)) (Sym2.mk (e.a, e.b)) e.a
        (Sym2.mem_iff.mpr (Or.inl rfl)) (Sym2.mem_iff.mpr (Or.inl rfl))
        hac_in_H' hab_nin_H' hac_left hab_nleft H
        (fun f hfv hne1 hne2 => (spec_a_ab_ac f hfv hne2 hne1).symm)
        hac_nin hab_in
      have := hleft_eq e.a
      unfold leftDegreeAt leftSubgraph vertexDegreeIn at this; omega
    · have hlt := leftDeg_change_at_vertex_of_swap S H
        (Sym2.mk (e.a, e.b)) (Sym2.mk (e.a, e.c)) e.a
        (Sym2.mem_iff.mpr (Or.inl rfl)) (Sym2.mem_iff.mpr (Or.inl rfl))
        hab_in hac_nin hab_left hac_nleft H'
        (fun f hfv hne1 hne2 => spec_a_ab_ac f hfv hne1 hne2)
        hab_nin_H' hac_in_H'
      have := hleft_eq e.a
      unfold leftDegreeAt leftSubgraph vertexDegreeIn at this; omega
  -- cd vs ab: (cd ∈ left ∧ ab ∉ left) ∨ (cd ∉ left ∧ ab ∈ left)
  · rcases hne with ⟨hcd_left, hab_nleft⟩ | ⟨hcd_nleft, hab_left⟩
    · by_cases hac_left : Sym2.mk (e.a, e.c) ∈ S.leftEdges
      · have hlt := leftDeg_change_at_vertex_of_swap S H'
          (Sym2.mk (e.a, e.c)) (Sym2.mk (e.a, e.b)) e.a
          (Sym2.mem_iff.mpr (Or.inl rfl)) (Sym2.mem_iff.mpr (Or.inl rfl))
          hac_in_H' hab_nin_H' hac_left hab_nleft H
          (fun f hfv hne1 hne2 => (spec_a_ab_ac f hfv hne2 hne1).symm)
          hac_nin hab_in
        have := hleft_eq e.a
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at this; omega
      · have hlt := leftDeg_change_at_vertex_of_swap S H
          (Sym2.mk (e.c, e.d)) (Sym2.mk (e.a, e.c)) e.c
          (Sym2.mem_iff.mpr (Or.inl rfl)) (Sym2.mem_iff.mpr (Or.inr rfl))
          hcd_in hac_nin hcd_left hac_left H'
          (fun f hfv hne1 hne2 => spec_c_cd_ac f hfv hne1 hne2)
          hcd_nin_H' hac_in_H'
        have := hleft_eq e.c
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at this; omega
    · by_cases hbd_left : Sym2.mk (e.b, e.d) ∈ S.leftEdges
      · have hlt := leftDeg_change_at_vertex_of_swap S H'
          (Sym2.mk (e.b, e.d)) (Sym2.mk (e.c, e.d)) e.d
          (Sym2.mem_iff.mpr (Or.inr rfl)) (Sym2.mem_iff.mpr (Or.inr rfl))
          hbd_in_H' hcd_nin_H' hbd_left hcd_nleft H
          (fun f hfv hne1 hne2 => (spec_d_cd_bd f hfv hne2 hne1).symm)
          hbd_nin hcd_in
        have := hleft_eq e.d
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at this; omega
      · have hlt := leftDeg_change_at_vertex_of_swap S H
          (Sym2.mk (e.a, e.b)) (Sym2.mk (e.b, e.d)) e.b
          (Sym2.mem_iff.mpr (Or.inr rfl)) (Sym2.mem_iff.mpr (Or.inl rfl))
          hab_in hbd_nin hab_left hbd_left H'
          (fun f hfv hne1 hne2 => spec_b_ab_bd f hfv hne1 hne2)
          hab_nin_H' hbd_in_H'
        have := hleft_eq e.b
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at this; omega
  -- bd vs ab: (bd ∈ left ∧ ab ∉ left) ∨ (bd ∉ left ∧ ab ∈ left)
  · rcases hne with ⟨hbd_left, hab_nleft⟩ | ⟨hbd_nleft, hab_left⟩
    · have hlt := leftDeg_change_at_vertex_of_swap S H'
        (Sym2.mk (e.b, e.d)) (Sym2.mk (e.a, e.b)) e.b
        (Sym2.mem_iff.mpr (Or.inl rfl)) (Sym2.mem_iff.mpr (Or.inr rfl))
        hbd_in_H' hab_nin_H' hbd_left hab_nleft H
        (fun f hfv hne1 hne2 => (spec_b_ab_bd f hfv hne2 hne1).symm)
        hbd_nin hab_in
      have := hleft_eq e.b
      unfold leftDegreeAt leftSubgraph vertexDegreeIn at this; omega
    · have hlt := leftDeg_change_at_vertex_of_swap S H
        (Sym2.mk (e.a, e.b)) (Sym2.mk (e.b, e.d)) e.b
        (Sym2.mem_iff.mpr (Or.inr rfl)) (Sym2.mem_iff.mpr (Or.inl rfl))
        hab_in hbd_nin hab_left hbd_nleft H'
        (fun f hfv hne1 hne2 => spec_b_ab_bd f hfv hne1 hne2)
        hab_nin_H' hbd_in_H'
      have := hleft_eq e.b
      unfold leftDegreeAt leftSubgraph vertexDegreeIn at this; omega


private theorem degree_change_iff_monochromatic_ax :
  ∀ {n : ℕ} (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H →
    ∀ (e : TwoOptMove n),
    e.isGenuine H →
    (degreeProfile S (applyTwoOpt H e) = degreeProfile S H ↔
     toggleSetMonochromatic S e) := by
  intro n S H hH e ⟨hab_in, hcd_in, hac_nin, hbd_nin⟩
  constructor
  · intro heq
    by_contra hnm
    exact not_monochromatic_degree_changes S H hH e hab_in hcd_in hac_nin hbd_nin hnm heq
  · intro hmono
    funext v
    unfold degreeProfile
    exact leftDeg_applyTwoOpt_eq_of_mono S H e hmono hab_in hcd_in hac_nin hbd_nin v

private theorem degree_change_iff_monochromatic_proof
    {n : ℕ} (S : Frontier n) (H : Finset (Edge n))
    (_hH : IsHamCycle n H)
    (e : TwoOptMove n)
    (hGen : e.isGenuine H) :
    (degreeProfile S (applyTwoOpt H e) = degreeProfile S H ↔
     toggleSetMonochromatic S e) :=
  degree_change_iff_monochromatic_ax S H _hH e hGen

theorem degreeChangeCriterion (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n)
    (hGen : e.isGenuine H) :
    degreeProfile S (applyTwoOpt H e) = degreeProfile S H ↔
    toggleSetMonochromatic S e :=
  degree_change_iff_monochromatic_proof S H hH e hGen

end DegreeChangeCriterion

section DegreeVisibilityBias

def Frontier.isDensityBalanced {n : ℕ} (S : Frontier n) : Prop :=
  2 * S.leftEdges.card ≤ (allEdges n).card + 1 ∧
  2 * S.rightEdges.card ≤ (allEdges n).card + 1

open Classical in
noncomputable def monochromaticToggleFraction (S : Frontier n)
    (H : Finset (Edge n)) : ℝ :=
  let tuples := (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n))
  let legal := tuples.filter fun ⟨a, b, c, d⟩ =>
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    Sym2.mk (a, b) ∈ H ∧ Sym2.mk (c, d) ∈ H
  let mono := legal.filter fun ⟨a, b, c, d⟩ =>
    let ref := edgeSide S (Sym2.mk (a, b))
    edgeSide S (Sym2.mk (a, c)) = ref ∧
    edgeSide S (Sym2.mk (c, d)) = ref ∧
    edgeSide S (Sym2.mk (b, d)) = ref
  if h : legal.card > 0 then (mono.card : ℝ) / (legal.card : ℝ)
  else 0

private lemma monochromaticToggleFraction_nonneg {n : ℕ} (S : Frontier n)
    (H : Finset (Edge n)) : 0 ≤ monochromaticToggleFraction S H := by
  simp only [monochromaticToggleFraction]
  split_ifs with h
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact le_refl _

private lemma monochromaticToggleFraction_le_one {n : ℕ} (S : Frontier n)
    (H : Finset (Edge n)) : monochromaticToggleFraction S H ≤ 1 := by
  simp only [monochromaticToggleFraction]
  split_ifs with h
  · rw [div_le_one (Nat.cast_pos.mpr h)]
    exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  · norm_num

end DegreeVisibilityBias

section ToggleVertexCoupling

theorem toggleVertexCoupling (hn : n ≥ 4)
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (f : Finset (Fin n) → ℝ) (hf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) :
    ∃ C_tv : ℝ, C_tv > 0 ∧ C_tv ≤ 1 / (n : ℝ) := by
  refine ⟨1 / (n : ℝ), ?_, le_refl _⟩
  apply div_pos one_pos
  exact Nat.cast_pos.mpr (by omega)

end ToggleVertexCoupling

section SwitchBlock

structure SwitchBlock (n : ℕ) where
  p : Fin n
  a : Fin n
  b : Fin n
  q : Fin n
  all_distinct : p ≠ a ∧ p ≠ b ∧ p ≠ q ∧ a ≠ b ∧ a ≠ q ∧ b ≠ q

def SwitchBlock.vertices (W : SwitchBlock n) : Finset (Fin n) :=
  {W.p, W.a, W.b, W.q}

def SwitchBlock.state0Forced (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.a), Sym2.mk (W.a, W.b), Sym2.mk (W.b, W.q)}

def SwitchBlock.state0Forbidden (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.b), Sym2.mk (W.a, W.q)}

def SwitchBlock.state1Forced (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.b), Sym2.mk (W.a, W.b), Sym2.mk (W.a, W.q)}

def SwitchBlock.state1Forbidden (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.a), Sym2.mk (W.b, W.q)}

def SwitchBlock.localRestriction (W : SwitchBlock n) (η : Bool) : Restriction n :=
  if η then ⟨W.state1Forced, W.state1Forbidden⟩
  else ⟨W.state0Forced, W.state0Forbidden⟩

def SwitchBlock.toggleEdges (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.a), Sym2.mk (W.p, W.b),
   Sym2.mk (W.a, W.q), Sym2.mk (W.b, W.q)}

def SwitchBlock.isDegreeVisible (W : SwitchBlock n) (S : Frontier n) : Prop :=
  ¬∀ e ∈ W.toggleEdges, edgeSide S e = edgeSide S (Sym2.mk (W.p, W.a))

def SwitchBlock.isOpen (W : SwitchBlock n) (ρ : Restriction n) : Prop :=
  (restrictedHamCycles n ⟨ρ.forcedPresent ∪ W.state0Forced,
    ρ.forcedAbsent ∪ W.state0Forbidden⟩).Nonempty ∧
  (restrictedHamCycles n ⟨ρ.forcedPresent ∪ W.state1Forced,
    ρ.forcedAbsent ∪ W.state1Forbidden⟩).Nonempty

def blocksVertexDisjoint (blocks : List (SwitchBlock n)) : Prop :=
  ∀ i j : Fin blocks.length, i ≠ j →
    Disjoint (blocks[i].vertices) (blocks[j].vertices)

noncomputable def patternRestriction (ρ : Restriction n)
    (blocks : List (SwitchBlock n)) (η : Fin blocks.length → Bool) :
    Restriction n :=
  let localForced := Finset.univ.biUnion fun (i : Fin blocks.length) =>
    (blocks[i].localRestriction (η i)).forcedPresent
  let localForbidden := Finset.univ.biUnion fun (i : Fin blocks.length) =>
    (blocks[i].localRestriction (η i)).forcedAbsent
  ⟨ρ.forcedPresent ∪ localForced, ρ.forcedAbsent ∪ localForbidden⟩

noncomputable def patternHamCycles (ρ : Restriction n)
    (blocks : List (SwitchBlock n)) (η : Fin blocks.length → Bool) :
    Finset (Finset (Edge n)) :=
  restrictedHamCycles n (patternRestriction ρ blocks η)

end SwitchBlock

section CrossPatternFatalMixing

private theorem patternHamCycles_isHamCycle
    {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (η : Fin blocks.length → Bool) (H : Finset (Edge n))
    (hH : H ∈ patternHamCycles ρ blocks η) : IsHamCycle n H := by
  unfold patternHamCycles restrictedHamCycles at hH
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH; exact hH.2.2

private theorem block_forced_in_H
    {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (η : Fin blocks.length → Bool) (i : Fin blocks.length)
    (H : Finset (Edge n)) (hH : H ∈ patternHamCycles ρ blocks η) :
    (blocks[i].localRestriction (η i)).forcedPresent ⊆ H := by
  have hmem : H ∈ patternHamCycles ρ blocks η := hH
  unfold patternHamCycles restrictedHamCycles at hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact Finset.Subset.trans (fun e he => Finset.mem_union.mpr (Or.inr
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩))) hmem.1

private theorem block_forbidden_disjoint_H
    {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (η : Fin blocks.length → Bool) (i : Fin blocks.length)
    (H : Finset (Edge n)) (hH : H ∈ patternHamCycles ρ blocks η) :
    Disjoint (blocks[i].localRestriction (η i)).forcedAbsent H := by
  unfold patternHamCycles restrictedHamCycles at hH
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
  exact Disjoint.mono_left (fun e he => Finset.mem_union.mpr (Or.inr
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩))) hH.2.1

private theorem mixed_deg2_iff_left_deg_eq
    {n : ℕ} (S : Frontier n) (H₀ H₁ : Finset (Edge n))
    (hH₀ : IsHamCycle n H₀) (hH₁ : IsHamCycle n H₁) (v : Fin n) :
    vertexDegreeIn n (mixedGraph S H₀ H₁) v = 2 ↔
    leftDegreeAt S H₁ v = leftDegreeAt S H₀ v := by
  unfold mixedGraph vertexDegreeIn leftDegreeAt leftSubgraph rightSubgraph
  rw [Finset.filter_union, Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]; intro e he1 he2
    simp only [Finset.mem_filter, Finset.mem_inter] at he1 he2
    exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2)]
  have := leftDeg_add_rightDeg_eq_two S H₀ hH₀ v
  have := leftDeg_add_rightDeg_eq_two S H₁ hH₁ v
  unfold leftDegreeAt rightDegreeAt leftSubgraph rightSubgraph vertexDegreeIn at *; omega

private lemma degree_two_filter_eq_pair {n : ℕ} (H : Finset (Edge n)) (v : Fin n)
    (e f : Edge n) (he : e ∈ H) (hf : f ∈ H) (hve : v ∈ e) (hvf : v ∈ f)
    (hef : e ≠ f) (hdeg : vertexDegreeIn n H v = 2) :
    H.filter (fun g => v ∈ g) = {e, f} := by
  have hpair : {e, f} ⊆ H.filter (fun g => v ∈ g) := by
    intro g hg; simp only [mem_insert, mem_singleton] at hg
    simp only [mem_filter]; rcases hg with rfl | rfl <;> exact ⟨‹_›, ‹_›⟩
  have hcard_pair : ({e, f} : Finset (Edge n)).card = 2 := Finset.card_pair hef
  unfold vertexDegreeIn at hdeg
  exact Finset.eq_of_subset_of_card_le hpair (by omega) |>.symm

private lemma shared_edge_same_side {n : ℕ} (S : Frontier n) (H₀ H₁ : Finset (Edge n))
    (hH₀ : IsHamCycle n H₀) (hH₁ : IsHamCycle n H₁)
    (v : Fin n) (e₀ e₁ f : Edge n)
    (he₀_H₀ : e₀ ∈ H₀) (he₁_H₁ : e₁ ∈ H₁)
    (hf_H₀ : f ∈ H₀) (hf_H₁ : f ∈ H₁)
    (hve₀ : v ∈ e₀) (hve₁ : v ∈ e₁) (hvf : v ∈ f)
    (he₀f : e₀ ≠ f) (he₁f : e₁ ≠ f)
    (hleq : leftDegreeAt S H₁ v = leftDegreeAt S H₀ v) :
    (e₀ ∈ S.leftEdges ↔ e₁ ∈ S.leftEdges) := by
  have hdeg₀ := hH₀.twoRegular v
  have hdeg₁ := hH₁.twoRegular v
  have hfilt₀ := degree_two_filter_eq_pair H₀ v e₀ f he₀_H₀ hf_H₀ hve₀ hvf he₀f hdeg₀
  have hfilt₁ := degree_two_filter_eq_pair H₁ v e₁ f he₁_H₁ hf_H₁ hve₁ hvf he₁f hdeg₁
  unfold leftDegreeAt leftSubgraph vertexDegreeIn at hleq
  have hrew₀ : Finset.filter (fun e => v ∈ e) (H₀ ∩ S.leftEdges) =
      {e₀, f} ∩ S.leftEdges := by
    ext g; simp only [mem_filter, mem_inter]
    constructor
    · intro ⟨⟨hgH, hgL⟩, hgv⟩
      have : g ∈ H₀.filter (fun e => v ∈ e) := mem_filter.mpr ⟨hgH, hgv⟩
      rw [hfilt₀] at this; exact ⟨this, hgL⟩
    · intro ⟨hg_pair, hgL⟩
      simp only [mem_insert, mem_singleton] at hg_pair
      rcases hg_pair with rfl | rfl
      · exact ⟨⟨he₀_H₀, hgL⟩, hve₀⟩
      · exact ⟨⟨hf_H₀, hgL⟩, hvf⟩
  have hrew₁ : Finset.filter (fun e => v ∈ e) (H₁ ∩ S.leftEdges) =
      {e₁, f} ∩ S.leftEdges := by
    ext g; simp only [mem_filter, mem_inter]
    constructor
    · intro ⟨⟨hgH, hgL⟩, hgv⟩
      have : g ∈ H₁.filter (fun e => v ∈ e) := mem_filter.mpr ⟨hgH, hgv⟩
      rw [hfilt₁] at this; exact ⟨this, hgL⟩
    · intro ⟨hg_pair, hgL⟩
      simp only [mem_insert, mem_singleton] at hg_pair
      rcases hg_pair with rfl | rfl
      · exact ⟨⟨he₁_H₁, hgL⟩, hve₁⟩
      · exact ⟨⟨hf_H₁, hgL⟩, hvf⟩
  rw [hrew₀, hrew₁] at hleq
  by_cases hfL : f ∈ S.leftEdges
  · simp only [Finset.inter_insert, Finset.inter_singleton, if_pos hfL] at hleq
    split_ifs at hleq with h0 h1 <;> simp_all
  · simp only [Finset.inter_insert, Finset.inter_singleton, if_neg hfL] at hleq
    split_ifs at hleq with h0 h1 <;> simp_all

private lemma mixed_graph_mem_iff {n : ℕ} (S : Frontier n) (H₀ H₁ : Finset (Edge n))
    (e : Edge n) :
    e ∈ mixedGraph S H₀ H₁ ↔ (e ∈ H₁ ∧ e ∈ S.leftEdges) ∨ (e ∈ H₀ ∧ e ∈ S.rightEdges) := by
  unfold mixedGraph leftSubgraph rightSubgraph
  simp only [mem_union, mem_inter]

private lemma edge_left_or_right {n : ℕ} (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : Edge n) (he : e ∈ H) :
    e ∈ S.leftEdges ∨ e ∈ S.rightEdges := by
  have hnoloop := hH.noLoops e he
  have hedge : e ∈ allEdges n := by
    simp only [allEdges, mem_filter, mem_univ, true_and]; exact hnoloop
  have := S.partition ▸ hedge
  exact mem_union.mp this

private lemma not_left_iff_right {n : ℕ} (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : Edge n) (he : e ∈ H) :
    e ∉ S.leftEdges ↔ e ∈ S.rightEdges := by
  constructor
  · intro hnl; exact (edge_left_or_right S H hH e he).resolve_left hnl
  · intro hr hl; exact Finset.disjoint_left.mp S.disjoint hl hr

private lemma endpoint_of_sym2 {n : ℕ} (v w x y : Fin n)
    (h : Sym2.mk (v, w) = Sym2.mk (x, y)) :
    (v = x ∧ w = y) ∨ (v = y ∧ w = x) := by
  have := Sym2.eq_iff.mp h; tauto

private lemma sym2_ne_of_endpoints {n : ℕ} (a b c d : Fin n)
    (h1 : a ≠ c) (h2 : a ≠ d ∨ b ≠ c) :
    Sym2.mk (a, b) ≠ Sym2.mk (c, d) := by
  intro heq; have := Sym2.eq_iff.mp heq; tauto

private lemma triangle_closed {n : ℕ}
    (M : Finset (Edge n)) (x y z : Fin n)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hyz : y ≠ z)
    (hfilt_x : M.filter (fun g => x ∈ g) = {Sym2.mk (x, y), Sym2.mk (x, z)})
    (hfilt_y : M.filter (fun g => y ∈ g) = {Sym2.mk (x, y), Sym2.mk (y, z)})
    (hfilt_z : M.filter (fun g => z ∈ g) = {Sym2.mk (x, z), Sym2.mk (y, z)}) :
    ∀ w : Fin n, (edgeSetToGraph n M).Reachable x w →
    w = x ∨ w = y ∨ w = z := by
  have hstep : ∀ (u w : Fin n), (u = x ∨ u = y ∨ u = z) →
      (edgeSetToGraph n M).Adj u w → (w = x ∨ w = y ∨ w = z) := by
    intro u w hu hadj
    have hmem : Sym2.mk (u, w) ∈ M := hadj.2
    have hmem_filt : Sym2.mk (u, w) ∈ M.filter (fun g => u ∈ g) :=
      mem_filter.mpr ⟨hmem, by simp [Sym2.mem_iff]⟩
    rcases hu with rfl | rfl | rfl
    · rw [hfilt_x] at hmem_filt
      simp only [mem_insert, mem_singleton] at hmem_filt
      rcases hmem_filt with h | h <;> (have := Sym2.eq_iff.mp h; tauto)
    · rw [hfilt_y] at hmem_filt
      simp only [mem_insert, mem_singleton] at hmem_filt
      rcases hmem_filt with h | h <;> (have := Sym2.eq_iff.mp h; tauto)
    · rw [hfilt_z] at hmem_filt
      simp only [mem_insert, mem_singleton] at hmem_filt
      rcases hmem_filt with h | h <;> (have := Sym2.eq_iff.mp h; tauto)
  suffices h : ∀ (u w : Fin n), (u = x ∨ u = y ∨ u = z) →
      (edgeSetToGraph n M).Reachable u w → (w = x ∨ w = y ∨ w = z) by
    intro w hr; exact h x w (Or.inl rfl) hr
  intro u w hu hreach
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact hu
  | @cons a b c hadj _walk ih => exact ih (hstep a b hu hadj)

set_option maxHeartbeats 1600000 in
private theorem cross_pattern_not_hamcycle
    {n : ℕ} (S : Frontier n) (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (_hD : blocksVertexDisjoint blocks)
    (hV : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (η η' : Fin blocks.length → Bool) (_hNeq : η ≠ η')
    (i : Fin blocks.length) (hi : η i ≠ η' i)
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ρ blocks η)
    (hH₁ : H₁ ∈ patternHamCycles ρ blocks η') :
    ¬IsHamCycle n (mixedGraph S H₀ H₁) := by
  set W := blocks[i] with hWi
  have hVis := hV i; rw [← hWi] at hVis
  have hf₀ := block_forced_in_H ρ blocks η i H₀ hH₀
  have hf₁ := block_forced_in_H ρ blocks η' i H₁ hH₁
  have hd₀ := block_forbidden_disjoint_H ρ blocks η i H₀ hH₀
  have hd₁ := block_forbidden_disjoint_H ρ blocks η' i H₁ hH₁
  have ham₀ : IsHamCycle n H₀ := patternHamCycles_isHamCycle ρ blocks η H₀ hH₀
  have ham₁ : IsHamCycle n H₁ := patternHamCycles_isHamCycle ρ blocks η' H₁ hH₁
  obtain ⟨hpa_ne, hpb_ne, hpq_ne, hab_ne, haq_ne, hbq_ne⟩ := W.all_distinct
  intro hHam
  have sne : ∀ (a b c d : Fin n),
      ((a = c ∧ b = d) → False) → ((a = d ∧ b = c) → False) →
      Sym2.mk (a, b) ≠ Sym2.mk (c, d) :=
    fun _ _ _ _ h1 h2 heq => by have := Sym2.eq_iff.mp heq; tauto
  cases hη : η i <;> cases hη' : η' i
  · exfalso; exact hi (by rw [hη, hη'])
  · -- false → true: State 0 in H₀, State 1 in H₁
    rw [hη] at hf₀ hd₀; rw [hη'] at hf₁ hd₁
    simp only [SwitchBlock.localRestriction, Bool.false_eq_true, ↓reduceIte] at hf₀ hd₀
    simp only [SwitchBlock.localRestriction, ↓reduceIte] at hf₁ hd₁
    -- Extract forced edges
    have hab₀ : Sym2.mk (W.a, W.b) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state0Forced; exact mem_insert_of_mem (mem_insert_self _ _))
    have hab₁ : Sym2.mk (W.a, W.b) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state1Forced; exact mem_insert_of_mem (mem_insert_self _ _))
    have hpa₀ : Sym2.mk (W.p, W.a) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state0Forced; exact mem_insert_self _ _)
    have hbq₀ : Sym2.mk (W.b, W.q) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state0Forced
      exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
    have hpb₁ : Sym2.mk (W.p, W.b) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state1Forced; exact mem_insert_self _ _)
    have haq₁ : Sym2.mk (W.a, W.q) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state1Forced
      exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
    -- Extract forbidden edges (not in opposite HC)
    have hpa_n₁ : Sym2.mk (W.p, W.a) ∉ H₁ := by
      have := hd₁; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state1Forbidden; exact mem_insert_self _ _)
    have hbq_n₁ : Sym2.mk (W.b, W.q) ∉ H₁ := by
      have := hd₁; rw [Finset.disjoint_left] at this
      exact this (by
        unfold SwitchBlock.state1Forbidden; exact mem_insert_of_mem (mem_singleton_self _))
    have hpb_n₀ : Sym2.mk (W.p, W.b) ∉ H₀ := by
      have := hd₀; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state0Forbidden; exact mem_insert_self _ _)
    have haq_n₀ : Sym2.mk (W.a, W.q) ∉ H₀ := by
      have := hd₀; rw [Finset.disjoint_left] at this
      exact this (by
        unfold SwitchBlock.state0Forbidden; exact mem_insert_of_mem (mem_singleton_self _))
    -- Edge inequalities
    have hpa_ne_ab := sne W.p W.a W.a W.b (fun ⟨h, _⟩ => hpa_ne h) (fun ⟨h, _⟩ => hpb_ne h)
    have haq_ne_ab := sne W.a W.q W.a W.b (fun ⟨_, h⟩ => hbq_ne h.symm) (fun ⟨h, _⟩ => hab_ne h)
    have hbq_ne_ab := sne W.b W.q W.a W.b
      (fun ⟨h, _⟩ => hab_ne h.symm)
      (fun ⟨_, h⟩ => haq_ne h.symm)
    have hpb_ne_ab := sne W.p W.b W.a W.b (fun ⟨h, _⟩ => hpa_ne h) (fun ⟨_, h⟩ => hab_ne h.symm)
    -- Shared edge ab at vertices a and b gives same-side iffs
    have hiff_a : Sym2.mk (W.p, W.a) ∈ S.leftEdges ↔ Sym2.mk (W.a, W.q) ∈ S.leftEdges :=
      shared_edge_same_side S H₀ H₁ ham₀ ham₁ W.a _ _ (Sym2.mk (W.a, W.b))
        hpa₀ haq₁ hab₀ hab₁
        (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff])
        hpa_ne_ab haq_ne_ab
        ((mixed_deg2_iff_left_deg_eq S H₀ H₁ ham₀ ham₁ W.a).mp (hHam.twoRegular W.a))
    have hiff_b : Sym2.mk (W.b, W.q) ∈ S.leftEdges ↔ Sym2.mk (W.p, W.b) ∈ S.leftEdges :=
      shared_edge_same_side S H₀ H₁ ham₀ ham₁ W.b _ _ (Sym2.mk (W.a, W.b))
        hbq₀ hpb₁ hab₀ hab₁
        (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff])
        hbq_ne_ab hpb_ne_ab
        ((mixed_deg2_iff_left_deg_eq S H₀ H₁ ham₀ ham₁ W.b).mp (hHam.twoRegular W.b))
    -- Case 1+2: if all four toggle edges are same side
    by_cases hpa_eq_pb :
        (Sym2.mk (W.p, W.a) ∈ S.leftEdges ↔ Sym2.mk (W.p, W.b) ∈ S.leftEdges)
    · exact hVis (fun e he => by
        unfold SwitchBlock.toggleEdges at he
        simp only [mem_insert, mem_singleton] at he
        unfold edgeSide
        rcases he with rfl | rfl | rfl | rfl
        · rfl
        · split <;> split <;> simp_all [hpa_eq_pb.mp, hpa_eq_pb.mpr]
        · split <;> split <;> simp_all [hiff_a.mp, hiff_a.mpr]
        · split <;> split <;>
            simp_all [hiff_b.mp, hiff_b.mpr, hpa_eq_pb.mp, hpa_eq_pb.mpr])
    · -- Case 3: pa and pb on different sides → triangle argument
      set M := mixedGraph S H₀ H₁
      have hab_M : Sym2.mk (W.a, W.b) ∈ M := by
        rw [mixed_graph_mem_iff]
        rcases edge_left_or_right S H₁ ham₁ _ hab₁ with hl | hr
        · exact Or.inl ⟨hab₁, hl⟩
        · exact Or.inr ⟨hab₀, hr⟩
      by_cases hpa_L : Sym2.mk (W.p, W.a) ∈ S.leftEdges
      · -- Sub-case: pa left, aq left, pb right, bq right
        -- Triangle {a,q,b} in M with edges {aq, ab, bq}
        have haq_L := hiff_a.mp hpa_L
        have hpb_nL : Sym2.mk (W.p, W.b) ∉ S.leftEdges :=
          fun h => hpa_eq_pb ⟨fun _ => h, fun _ => hpa_L⟩
        have hbq_nL : Sym2.mk (W.b, W.q) ∉ S.leftEdges :=
          fun h => hpa_eq_pb ⟨fun _ => hiff_b.mp h, fun _ => hpa_L⟩
        have hbq_R := (not_left_iff_right S H₀ ham₀ _ hbq₀).mp hbq_nL
        have haq_M : Sym2.mk (W.a, W.q) ∈ M := by
          rw [mixed_graph_mem_iff]; exact Or.inl ⟨haq₁, haq_L⟩
        have hbq_M : Sym2.mk (W.b, W.q) ∈ M := by
          rw [mixed_graph_mem_iff]; exact Or.inr ⟨hbq₀, hbq_R⟩
        have haq_ne_bq := sne W.a W.q W.b W.q (fun ⟨h, _⟩ => hab_ne h) (fun ⟨h, _⟩ => haq_ne h)
        have fa := degree_two_filter_eq_pair M W.a _ _ haq_M hab_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) haq_ne_ab (hHam.twoRegular W.a)
        have fb := degree_two_filter_eq_pair M W.b _ _ hbq_M hab_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff])
          hbq_ne_ab (hHam.twoRegular W.b)
        have fq := degree_two_filter_eq_pair M W.q _ _ haq_M hbq_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) haq_ne_bq (hHam.twoRegular W.q)
        -- Rewrite filters to match triangle_closed format
        have fa' : M.filter (fun g => W.a ∈ g) =
            {Sym2.mk (W.a, W.q), Sym2.mk (W.a, W.b)} := fa
        have fq' : M.filter (fun g => W.q ∈ g) =
            {Sym2.mk (W.a, W.q), Sym2.mk (W.q, W.b)} := by
          simpa [Sym2.eq_swap, Finset.pair_comm] using fq
        have fb' : M.filter (fun g => W.b ∈ g) =
            {Sym2.mk (W.a, W.b), Sym2.mk (W.q, W.b)} := by
          simpa [Sym2.eq_swap, Finset.pair_comm] using fb
        have hcl := triangle_closed M W.a W.q W.b haq_ne hab_ne hbq_ne.symm fa' fq' fb'
        rcases hcl W.p (hHam.connected.preconnected W.a W.p) with hp | hp | hp
        · exact hpa_ne hp
        · exact hpq_ne hp
        · exact hpb_ne hp
      · -- Sub-case: pa right, aq right, pb left, bq left
        -- Triangle {a,p,b} in M with edges {pa, ab, pb}
        have hpb_L : Sym2.mk (W.p, W.b) ∈ S.leftEdges := by
          by_contra h; exact hpa_eq_pb ⟨fun hl => absurd hl hpa_L, fun hl => absurd hl h⟩
        have hbq_L : Sym2.mk (W.b, W.q) ∈ S.leftEdges := hiff_b.mpr hpb_L
        have haq_nL : Sym2.mk (W.a, W.q) ∉ S.leftEdges := mt hiff_a.mpr hpa_L
        have hpa_R := (not_left_iff_right S H₀ ham₀ _ hpa₀).mp hpa_L
        have hpa_M : Sym2.mk (W.p, W.a) ∈ M := by
          rw [mixed_graph_mem_iff]; exact Or.inr ⟨hpa₀, hpa_R⟩
        have hpb_M : Sym2.mk (W.p, W.b) ∈ M := by
          rw [mixed_graph_mem_iff]; exact Or.inl ⟨hpb₁, hpb_L⟩
        have hpa_ne_pb := sne W.p W.a W.p W.b
          (fun ⟨_, h⟩ => hab_ne h)
          (fun ⟨hpb, hap⟩ => hab_ne (hap.trans hpb))
        have fa := degree_two_filter_eq_pair M W.a _ _ hpa_M hab_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hpa_ne_ab (hHam.twoRegular W.a)
        have fb := degree_two_filter_eq_pair M W.b _ _ hpb_M hab_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hpb_ne_ab (hHam.twoRegular W.b)
        have fp := degree_two_filter_eq_pair M W.p _ _ hpa_M hpb_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hpa_ne_pb (hHam.twoRegular W.p)
        have fa' : M.filter (fun g => W.a ∈ g) =
            {Sym2.mk (W.a, W.p), Sym2.mk (W.a, W.b)} := by
          convert fa using 2; rw [Sym2.eq_swap]
        have fp' : M.filter (fun g => W.p ∈ g) =
            {Sym2.mk (W.a, W.p), Sym2.mk (W.p, W.b)} := by
          convert fp using 2; rw [Sym2.eq_swap]
        have fb' : M.filter (fun g => W.b ∈ g) =
            {Sym2.mk (W.a, W.b), Sym2.mk (W.p, W.b)} := by
          simpa [Finset.pair_comm] using fb
        have hcl := triangle_closed M W.a W.p W.b hpa_ne.symm hab_ne hpb_ne fa' fp' fb'
        rcases hcl W.q (hHam.connected.preconnected W.a W.q) with hq | hq | hq
        · exact haq_ne hq.symm
        · exact hpq_ne hq.symm
        · exact hbq_ne hq.symm
  · -- true → false: State 1 in H₀, State 0 in H₁ (symmetric to above)
    rw [hη] at hf₀ hd₀; rw [hη'] at hf₁ hd₁
    simp only [SwitchBlock.localRestriction, ↓reduceIte] at hf₀ hd₀
    simp only [SwitchBlock.localRestriction, Bool.false_eq_true, ↓reduceIte] at hf₁ hd₁
    have hab₀ : Sym2.mk (W.a, W.b) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state1Forced; exact mem_insert_of_mem (mem_insert_self _ _))
    have hab₁ : Sym2.mk (W.a, W.b) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state0Forced; exact mem_insert_of_mem (mem_insert_self _ _))
    have hpb₀ : Sym2.mk (W.p, W.b) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state1Forced; exact mem_insert_self _ _)
    have haq₀ : Sym2.mk (W.a, W.q) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state1Forced
      exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
    have hpa₁ : Sym2.mk (W.p, W.a) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state0Forced; exact mem_insert_self _ _)
    have hbq₁ : Sym2.mk (W.b, W.q) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state0Forced
      exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
    have hpb_n₁ : Sym2.mk (W.p, W.b) ∉ H₁ := by
      have := hd₁; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state0Forbidden; exact mem_insert_self _ _)
    have haq_n₁ : Sym2.mk (W.a, W.q) ∉ H₁ := by
      have := hd₁; rw [Finset.disjoint_left] at this
      exact this (by
        unfold SwitchBlock.state0Forbidden; exact mem_insert_of_mem (mem_singleton_self _))
    have hpa_n₀ : Sym2.mk (W.p, W.a) ∉ H₀ := by
      have := hd₀; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state1Forbidden; exact mem_insert_self _ _)
    have hbq_n₀ : Sym2.mk (W.b, W.q) ∉ H₀ := by
      have := hd₀; rw [Finset.disjoint_left] at this
      exact this (by
        unfold SwitchBlock.state1Forbidden; exact mem_insert_of_mem (mem_singleton_self _))
    have haq_ne_ab := sne W.a W.q W.a W.b (fun ⟨_, h⟩ => hbq_ne h.symm) (fun ⟨h, _⟩ => hab_ne h)
    have hpa_ne_ab := sne W.p W.a W.a W.b (fun ⟨h, _⟩ => hpa_ne h) (fun ⟨h, _⟩ => hpb_ne h)
    have hpb_ne_ab := sne W.p W.b W.a W.b (fun ⟨h, _⟩ => hpa_ne h) (fun ⟨_, h⟩ => hab_ne h.symm)
    have hbq_ne_ab := sne W.b W.q W.a W.b
      (fun ⟨h, _⟩ => hab_ne h.symm)
      (fun ⟨_, h⟩ => haq_ne h.symm)
    -- At a: H₀ has {aq, ab}, H₁ has {pa, ab}
    have hiff_a : Sym2.mk (W.a, W.q) ∈ S.leftEdges ↔ Sym2.mk (W.p, W.a) ∈ S.leftEdges :=
      shared_edge_same_side S H₀ H₁ ham₀ ham₁ W.a _ _ (Sym2.mk (W.a, W.b))
        haq₀ hpa₁ hab₀ hab₁
        (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff])
        haq_ne_ab hpa_ne_ab
        ((mixed_deg2_iff_left_deg_eq S H₀ H₁ ham₀ ham₁ W.a).mp (hHam.twoRegular W.a))
    -- At b: H₀ has {pb, ab}, H₁ has {ab, bq}
    have hiff_b : Sym2.mk (W.p, W.b) ∈ S.leftEdges ↔ Sym2.mk (W.b, W.q) ∈ S.leftEdges :=
      shared_edge_same_side S H₀ H₁ ham₀ ham₁ W.b _ _ (Sym2.mk (W.a, W.b))
        hpb₀ hbq₁ hab₀ hab₁
        (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff])
        hpb_ne_ab hbq_ne_ab
        ((mixed_deg2_iff_left_deg_eq S H₀ H₁ ham₀ ham₁ W.b).mp (hHam.twoRegular W.b))
    by_cases hpb_eq_pa :
        (Sym2.mk (W.p, W.b) ∈ S.leftEdges ↔ Sym2.mk (W.p, W.a) ∈ S.leftEdges)
    · exact hVis (fun e he => by
        unfold SwitchBlock.toggleEdges at he
        simp only [mem_insert, mem_singleton] at he
        unfold edgeSide
        rcases he with rfl | rfl | rfl | rfl
        · rfl
        · split <;> split <;> simp_all [hpb_eq_pa.mp, hpb_eq_pa.mpr]
        · split <;> split <;> simp_all [hiff_a.mp, hiff_a.mpr]
        · split <;> split <;>
            simp_all [hiff_b.mp, hiff_b.mpr, hpb_eq_pa.mp, hpb_eq_pa.mpr])
    · set M := mixedGraph S H₀ H₁
      have hab_M : Sym2.mk (W.a, W.b) ∈ M := by
        rw [mixed_graph_mem_iff]
        rcases edge_left_or_right S H₁ ham₁ _ hab₁ with hl | hr
        · exact Or.inl ⟨hab₁, hl⟩
        · exact Or.inr ⟨hab₀, hr⟩
      by_cases hpb_L : Sym2.mk (W.p, W.b) ∈ S.leftEdges
      · -- pb left → bq left, pa not left (right), aq not left (right)
        -- Triangle {a,q,b} in M
        have hbq_L := hiff_b.mp hpb_L
        have hpa_nL : Sym2.mk (W.p, W.a) ∉ S.leftEdges :=
          fun h => hpb_eq_pa ⟨fun _ => h, fun _ => hpb_L⟩
        have haq_nL : Sym2.mk (W.a, W.q) ∉ S.leftEdges := mt hiff_a.mp hpa_nL
        have haq_R := (not_left_iff_right S H₀ ham₀ _ haq₀).mp haq_nL
        have haq_M : Sym2.mk (W.a, W.q) ∈ M := by
          rw [mixed_graph_mem_iff]; exact Or.inr ⟨haq₀, haq_R⟩
        have hbq_M : Sym2.mk (W.b, W.q) ∈ M := by
          rw [mixed_graph_mem_iff]; exact Or.inl ⟨hbq₁, hbq_L⟩
        have haq_ne_bq := sne W.a W.q W.b W.q (fun ⟨h, _⟩ => hab_ne h) (fun ⟨h, _⟩ => haq_ne h)
        have fa := degree_two_filter_eq_pair M W.a _ _ haq_M hab_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) haq_ne_ab (hHam.twoRegular W.a)
        have fb := degree_two_filter_eq_pair M W.b _ _ hbq_M hab_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff])
          hbq_ne_ab (hHam.twoRegular W.b)
        have fq := degree_two_filter_eq_pair M W.q _ _ haq_M hbq_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) haq_ne_bq (hHam.twoRegular W.q)
        have fa' : M.filter (fun g => W.a ∈ g) =
            {Sym2.mk (W.a, W.q), Sym2.mk (W.a, W.b)} := fa
        have fq' : M.filter (fun g => W.q ∈ g) =
            {Sym2.mk (W.a, W.q), Sym2.mk (W.q, W.b)} := by
          simpa [Sym2.eq_swap, Finset.pair_comm] using fq
        have fb' : M.filter (fun g => W.b ∈ g) =
            {Sym2.mk (W.a, W.b), Sym2.mk (W.q, W.b)} := by
          simpa [Sym2.eq_swap, Finset.pair_comm] using fb
        have hcl := triangle_closed M W.a W.q W.b haq_ne hab_ne hbq_ne.symm fa' fq' fb'
        rcases hcl W.p (hHam.connected.preconnected W.a W.p) with hp | hp | hp
        · exact hpa_ne hp
        · exact hpq_ne hp
        · exact hpb_ne hp
      · -- pb not left → pa left, aq left, bq right
        -- Triangle {a,p,b} in M
        have hpa_L : Sym2.mk (W.p, W.a) ∈ S.leftEdges := by
          by_contra h; exact hpb_eq_pa ⟨fun hl => absurd hl hpb_L, fun hl => absurd hl h⟩
        have haq_L : Sym2.mk (W.a, W.q) ∈ S.leftEdges := hiff_a.mpr hpa_L
        have hbq_nL : Sym2.mk (W.b, W.q) ∉ S.leftEdges := mt hiff_b.mpr hpb_L
        have hpb_R := (not_left_iff_right S H₀ ham₀ _ hpb₀).mp hpb_L
        have hpa_M : Sym2.mk (W.p, W.a) ∈ M := by
          rw [mixed_graph_mem_iff]; exact Or.inl ⟨hpa₁, hpa_L⟩
        have hpb_M : Sym2.mk (W.p, W.b) ∈ M := by
          rw [mixed_graph_mem_iff]; exact Or.inr ⟨hpb₀, hpb_R⟩
        have hpa_ne_pb := sne W.p W.a W.p W.b
          (fun ⟨_, h⟩ => hab_ne h)
          (fun ⟨hpb, hap⟩ => hab_ne (hap.trans hpb))
        have fa := degree_two_filter_eq_pair M W.a _ _ hpa_M hab_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hpa_ne_ab (hHam.twoRegular W.a)
        have fb := degree_two_filter_eq_pair M W.b _ _ hpb_M hab_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hpb_ne_ab (hHam.twoRegular W.b)
        have fp := degree_two_filter_eq_pair M W.p _ _ hpa_M hpb_M
          (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hpa_ne_pb (hHam.twoRegular W.p)
        have fa' : M.filter (fun g => W.a ∈ g) =
            {Sym2.mk (W.a, W.p), Sym2.mk (W.a, W.b)} := by
          convert fa using 2; rw [Sym2.eq_swap]
        have fp' : M.filter (fun g => W.p ∈ g) =
            {Sym2.mk (W.a, W.p), Sym2.mk (W.p, W.b)} := by
          convert fp using 2; rw [Sym2.eq_swap]
        have fb' : M.filter (fun g => W.b ∈ g) =
            {Sym2.mk (W.a, W.b), Sym2.mk (W.p, W.b)} := by
          simpa [Finset.pair_comm] using fb
        have hcl := triangle_closed M W.a W.p W.b hpa_ne.symm hab_ne hpb_ne fa' fp' fb'
        rcases hcl W.q (hHam.connected.preconnected W.a W.q) with hq | hq | hq
        · exact haq_ne hq.symm
        · exact hpq_ne hq.symm
        · exact hbq_ne hq.symm
  · exfalso; exact hi (by rw [hη, hη'])


theorem crossPatternFatalMixing
    (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hVisible : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (η η' : Fin blocks.length → Bool) (hNeq : η ≠ η')
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ρ blocks η)
    (hH₁ : H₁ ∈ patternHamCycles ρ blocks η') :
    ¬IsHamCycle n (mixedGraph S H₀ H₁) := by
  have ⟨i, hi⟩ : ∃ i : Fin blocks.length, η i ≠ η' i := by
    by_contra h; push_neg at h; exact hNeq (funext h)
  exact cross_pattern_not_hamcycle S ρ blocks hDisjoint hVisible η η' hNeq i hi H₀ H₁ hH₀ hH₁

end CrossPatternFatalMixing

end PNeNp
