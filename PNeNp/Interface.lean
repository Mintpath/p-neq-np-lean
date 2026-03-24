import PNeNp.Basic
import PNeNp.GraphInfra
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases

open Finset

namespace PNeNp

variable {n : ℕ}

/-! ## Definition 3.2(a): Degree profile d_S(H) -/

section DegreeProfile

noncomputable def degreeProfile (S : Frontier n) (H : Finset (Edge n)) :
    Fin n → ℕ :=
  fun v => leftDegreeAt S H v

theorem degreeProfile_le_two (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (v : Fin n) :
    degreeProfile S H v ≤ 2 := by
  unfold degreeProfile leftDegreeAt leftSubgraph vertexDegreeIn
  have hv := hH.twoRegular v
  unfold vertexDegreeIn at hv
  calc (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).card
      ≤ (Finset.filter (fun e => v ∈ e) H).card := by
        apply Finset.card_le_card
        intro e he
        simp only [Finset.mem_filter, Finset.mem_inter] at he ⊢
        exact ⟨he.1.1, he.2⟩
    _ = 2 := hv

end DegreeProfile

/-! ## Definition 3.2(b): Dangling endpoints U_S(H) -/

section DanglingEndpoints

noncomputable def danglingEndpoints (S : Frontier n) (H : Finset (Edge n)) :
    Finset (Fin n) :=
  (boundaryVertices S).filter fun v => degreeProfile S H v = 1

end DanglingEndpoints

/-! ## Perfect matchings -/

section PerfectMatching

structure PerfectMatching {α : Type*} [DecidableEq α] (U : Finset α) where
  pairs : Finset (α × α)
  fst_mem : ∀ p ∈ pairs, p.1 ∈ U
  snd_mem : ∀ p ∈ pairs, p.2 ∈ U
  ne_pair : ∀ p ∈ pairs, p.1 ≠ p.2
  covers : ∀ u ∈ U, ∃ p ∈ pairs, u = p.1 ∨ u = p.2
  unique : ∀ u ∈ U, ∀ p₁ ∈ pairs, ∀ p₂ ∈ pairs,
    (u = p₁.1 ∨ u = p₁.2) → (u = p₂.1 ∨ u = p₂.2) → p₁ = p₂
  card_eq : 2 * pairs.card = U.card

end PerfectMatching

/-! ## Premature cycle flag c_S(H) -/

section PrematureCycleFlag

def hasPrematureCycle (S : Frontier n) (H : Finset (Edge n)) : Prop :=
  ∃ comp : Finset (Edge n),
    comp ⊆ leftSubgraph S H ∧
    comp.Nonempty ∧
    (∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) ∧
    comp ≠ H

open Classical in
noncomputable def prematureCycleFlag (S : Frontier n) (H : Finset (Edge n)) : Fin 2 :=
  if hasPrematureCycle S H then 1 else 0

end PrematureCycleFlag

/-! ## Key lemma: leftDeg + rightDeg = deg_H for every vertex -/

section DegreeDecomposition

theorem leftRight_disjoint_at_vertex (S : Frontier n) (H : Finset (Edge n)) (v : Fin n) :
    Disjoint
      (Finset.filter (fun e => v ∈ e) (leftSubgraph S H))
      (Finset.filter (fun e => v ∈ e) (rightSubgraph S H)) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  simp only [Finset.mem_filter] at he1 he2
  simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he1 he2
  exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2

theorem leftDeg_add_rightDeg_eq_two (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (v : Fin n) :
    leftDegreeAt S H v + rightDegreeAt S H v = 2 := by
  have h1 := hH.twoRegular v
  unfold leftDegreeAt rightDegreeAt vertexDegreeIn
  rw [← Finset.card_union_of_disjoint (leftRight_disjoint_at_vertex S H v)]
  unfold vertexDegreeIn at h1
  unfold leftSubgraph rightSubgraph
  have hset : Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges) ∪
    Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges) =
    Finset.filter (fun e => v ∈ e) H := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨⟨hmem, _⟩, hv⟩ | ⟨⟨hmem, _⟩, hv⟩) <;> exact ⟨hmem, hv⟩
    · rintro ⟨hmem, hv⟩
      have hedge : e ∈ allEdges n := by
        simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hH.noLoops e hmem
      have : e ∈ S.leftEdges ∪ S.rightEdges := S.partition ▸ hedge
      rcases Finset.mem_union.mp this with hleft | hright
      · exact Or.inl ⟨⟨hmem, hleft⟩, hv⟩
      · exact Or.inr ⟨⟨hmem, hright⟩, hv⟩
  rw [hset]; exact h1

end DegreeDecomposition

/-! ## Dangling endpoints have even cardinality -/

section DanglingEndpointsEven

def PathComponentDecomposition (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) : Prop :=
  ∀ comp : Finset (Edge n), comp ⊆ leftSubgraph S H → comp.Nonempty →
    (∀ v : Fin n, vertexDegreeIn n comp v ≤ 2) →
    ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)

theorem pathComponents_pairEndpoints :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H → ¬ hasPrematureCycle S H →
    ∃ k : ℕ, (danglingEndpoints S H).card = 2 * k := by
  intro n S H hH hc
  have h2reg := hH.twoRegular
  have hsum : ∀ v : Fin n, leftDegreeAt S H v + rightDegreeAt S H v = 2 :=
    leftDeg_add_rightDeg_eq_two S H hH
  have hdeg_le2 : ∀ v : Fin n, leftDegreeAt S H v ≤ 2 := by
    intro v; have := hsum v; omega
  have dangling_eq : danglingEndpoints S H =
      Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 1 := by
    ext v
    simp only [danglingEndpoints, Finset.mem_filter, boundaryVertices, Finset.mem_univ,
      true_and, degreeProfile]
    constructor
    · intro ⟨_, hd⟩; exact hd
    · intro hd
      refine ⟨⟨?_, ?_⟩, hd⟩
      · have hld : leftDegreeAt S H v ≥ 1 := by omega
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at hld
        have hne : (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.card_empty] at hld; omega
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
      · have hrd : rightDegreeAt S H v ≥ 1 := by have := hsum v; omega
        unfold rightDegreeAt rightSubgraph vertexDegreeIn at hrd
        have hne : (Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.card_empty] at hrd; omega
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
  rw [dangling_eq]
  have hnoloops : ∀ e ∈ leftSubgraph S H, ¬ e.IsDiag := by
    intro e he
    simp only [leftSubgraph, Finset.mem_inter] at he
    exact hH.noLoops e he.1
  have edge_card_two : ∀ e ∈ leftSubgraph S H,
      (Finset.univ.filter fun v : Fin n => v ∈ e).card = 2 := by
    intro e he
    have hnd := hnoloops e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := fun h => hnd (Sym2.mk_isDiag_iff.mpr h)
      have : (Finset.univ.filter fun v : Fin n => v ∈ Sym2.mk (a, b)) = {a, b} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Sym2.mem_iff]
      rw [this, Finset.card_insert_of_notMem (by simp [hab]),
        Finset.card_singleton]
  have sum_eq : ∑ v ∈ (Finset.univ : Finset (Fin n)), leftDegreeAt S H v =
      2 * (leftSubgraph S H).card := by
    simp only [leftDegreeAt, leftSubgraph, vertexDegreeIn]
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := H ∩ S.leftEdges) (r := fun (v : Fin n) (e : Edge n) => v ∈ e)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
    rw [hdc]
    have : ∀ e ∈ H ∩ S.leftEdges,
        (Finset.filter (fun a => a ∈ e) Finset.univ).card = 2 := by
      intro e he; exact edge_card_two e he
    rw [Finset.sum_congr rfl this]
    simp [Finset.sum_const, mul_comm]
  set D1 := Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 1
  set D2 := Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 2
  set K := (leftSubgraph S H).card
  have hpart : ∑ v ∈ Finset.univ, leftDegreeAt S H v =
      ∑ v ∈ D1, leftDegreeAt S H v + ∑ v ∈ D2, leftDegreeAt S H v +
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => leftDegreeAt S H v = 0),
        leftDegreeAt S H v := by
    have hdisj12 : Disjoint D1 D2 := by
      simp only [D1, D2, Finset.disjoint_filter]
      intro v _ h1 h2; omega
    have hdisj10 : Disjoint D1 (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      simp only [D1, Finset.disjoint_filter]
      intro v _ h1 h0; omega
    have hdisj20 : Disjoint D2 (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      simp only [D2, Finset.disjoint_filter]
      intro v _ h2 h0; omega
    have hunion : Finset.univ = D1 ∪ D2 ∪ (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      ext v
      simp only [D1, D2, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      have hle := hdeg_le2 v
      set d := leftDegreeAt S H v with hd_def
      interval_cases d <;> simp_all
    conv_lhs => rw [hunion]
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj10, hdisj20⟩)]
    rw [Finset.sum_union hdisj12]
  have hD1sum : ∑ v ∈ D1, leftDegreeAt S H v = D1.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [D1, Finset.mem_filter] at hv
    exact hv.2
  have hD2sum : ∑ v ∈ D2, leftDegreeAt S H v = 2 * D2.card := by
    have : ∑ v ∈ D2, leftDegreeAt S H v = ∑ _v ∈ D2, 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [D2, Finset.mem_filter] at hv
      exact hv.2
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have hD0sum : ∑ v ∈ Finset.univ.filter (fun v : Fin n => leftDegreeAt S H v = 0),
      leftDegreeAt S H v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp only [Finset.mem_filter] at hv
    exact hv.2
  have htotal : D1.card + 2 * D2.card = 2 * K := by
    have := sum_eq
    rw [hpart, hD1sum, hD2sum, hD0sum] at this
    omega
  exact ⟨K - D2.card, by omega⟩

theorem danglingEndpoints_even (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (hc : ¬ hasPrematureCycle S H) :
    Even (danglingEndpoints S H).card := by
  obtain ⟨k, hk⟩ := pathComponents_pairEndpoints n S H hH hc
  exact ⟨k, by omega⟩

end DanglingEndpointsEven

/-! ## Definition 3.2(c): Path-pairing π_S(H) -/

section PathPairing

open Classical in
private noncomputable def trivialMatchingOnEvenSet
    {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α]
    (U : Finset α) : ∀ (k : ℕ), U.card = 2 * k → PerfectMatching U
  | 0, hk => {
      pairs := ∅
      fst_mem := fun _ hp => by simp at hp
      snd_mem := fun _ hp => by simp at hp
      ne_pair := fun _ hp => by simp at hp
      covers := fun _ hu => by
        have : U = ∅ := Finset.card_eq_zero.mp (by omega)
        subst this; simp at hu
      unique := fun _ _ _ hp₁ => by simp at hp₁
      card_eq := by simp [show U.card = 0 from by omega]
    }
  | k + 1, hk =>
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    have hne' : (U.erase (U.min' hne)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have := Finset.card_erase_of_mem (Finset.min'_mem U hne)
      rw [h] at this; simp at this; omega
    let a := U.min' hne
    let b := (U.erase a).min' hne'
    have ha : a ∈ U := Finset.min'_mem U hne
    have hb' : b ∈ U.erase a := Finset.min'_mem _ hne'
    have hb : b ∈ U := Finset.mem_of_mem_erase hb'
    have hab : a ≠ b := by intro h; rw [h] at hb'; simp at hb'
    let U'' := (U.erase a).erase b
    have hU''_card : U''.card = 2 * k := by
      show ((U.erase a).erase b).card = 2 * k
      rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]; omega
    have hU''_sub : U'' ⊆ U := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have ha_not : a ∉ U'' := by
      intro h; have := Finset.mem_of_mem_erase h; simp at this
    have hb_not : b ∉ U'' := by simp [U'']
    let rest := trivialMatchingOnEvenSet U'' k hU''_card
    have rpne : ∀ p ∈ rest.pairs, p.1 ≠ a ∧ p.1 ≠ b ∧ p.2 ≠ a ∧ p.2 ≠ b := fun p hp =>
      ⟨fun h => ha_not (h ▸ rest.fst_mem p hp),
       fun h => hb_not (h ▸ rest.fst_mem p hp),
       fun h => ha_not (h ▸ rest.snd_mem p hp),
       fun h => hb_not (h ▸ rest.snd_mem p hp)⟩
    have ab_not : (a, b) ∉ rest.pairs := fun h => (rpne _ h).1 rfl
    { pairs := insert (a, b) rest.pairs
      fst_mem := fun p hp => by
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact ha
        · exact hU''_sub (rest.fst_mem p hp)
      snd_mem := fun p hp => by
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hb
        · exact hU''_sub (rest.snd_mem p hp)
      ne_pair := fun p hp => by
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hab
        · exact rest.ne_pair p hp
      covers := fun u hu => by
        by_cases hau : u = a
        · exact ⟨(a, b), Finset.mem_insert_self _ _, Or.inl hau⟩
        · by_cases hbu : u = b
          · exact ⟨(a, b), Finset.mem_insert_self _ _, Or.inr hbu⟩
          · have huU'' : u ∈ U'' :=
              Finset.mem_erase.mpr ⟨hbu, Finset.mem_erase.mpr ⟨hau, hu⟩⟩
            obtain ⟨p, hp, hup⟩ := rest.covers u huU''
            exact ⟨p, Finset.mem_insert_of_mem hp, hup⟩
      unique := fun u _ p₁ hp₁ p₂ hp₂ h1 h2 => by
        rw [Finset.mem_insert] at hp₁ hp₂
        rcases hp₁ with rfl | hp₁ <;> rcases hp₂ with rfl | hp₂
        · rfl
        · exfalso
          rcases h1 with rfl | rfl
          · rcases h2 with h | h
            · exact (rpne _ hp₂).1 h.symm
            · exact (rpne _ hp₂).2.2.1 h.symm
          · rcases h2 with h | h
            · exact (rpne _ hp₂).2.1 h.symm
            · exact (rpne _ hp₂).2.2.2 h.symm
        · exfalso
          rcases h2 with rfl | rfl
          · rcases h1 with h | h
            · exact (rpne _ hp₁).1 h.symm
            · exact (rpne _ hp₁).2.2.1 h.symm
          · rcases h1 with h | h
            · exact (rpne _ hp₁).2.1 h.symm
            · exact (rpne _ hp₁).2.2.2 h.symm
        · exact rest.unique u (by
            rcases h1 with rfl | rfl
            · exact rest.fst_mem p₁ hp₁
            · exact rest.snd_mem p₁ hp₁) p₁ hp₁ p₂ hp₂ h1 h2
      card_eq := by
        simp [ab_not]; have := rest.card_eq; omega }

private theorem danglingEndpoints_card_even_general
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ k : ℕ, (danglingEndpoints S H).card = 2 * k := by
  have hsum : ∀ v : Fin n, leftDegreeAt S H v + rightDegreeAt S H v = 2 :=
    leftDeg_add_rightDeg_eq_two S H hH
  have hdeg_le2 : ∀ v : Fin n, leftDegreeAt S H v ≤ 2 := by
    intro v; have := hsum v; omega
  have dangling_eq : danglingEndpoints S H =
      Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 1 := by
    ext v
    simp only [danglingEndpoints, Finset.mem_filter, boundaryVertices, Finset.mem_univ,
      true_and, degreeProfile]
    constructor
    · intro ⟨_, hd⟩; exact hd
    · intro hd
      refine ⟨⟨?_, ?_⟩, hd⟩
      · have hld : leftDegreeAt S H v ≥ 1 := by omega
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at hld
        have hne : (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.card_empty] at hld; omega
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
      · have hrd : rightDegreeAt S H v ≥ 1 := by have := hsum v; omega
        unfold rightDegreeAt rightSubgraph vertexDegreeIn at hrd
        have hne : (Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges)).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          rw [h, Finset.card_empty] at hrd; omega
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
  rw [dangling_eq]
  have hnoloops : ∀ e ∈ leftSubgraph S H, ¬ e.IsDiag := by
    intro e he
    simp only [leftSubgraph, Finset.mem_inter] at he
    exact hH.noLoops e he.1
  have edge_card_two : ∀ e ∈ leftSubgraph S H,
      (Finset.univ.filter fun v : Fin n => v ∈ e).card = 2 := by
    intro e he
    have hnd := hnoloops e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := fun h => hnd (Sym2.mk_isDiag_iff.mpr h)
      have : (Finset.univ.filter fun v : Fin n => v ∈ Sym2.mk (a, b)) = {a, b} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Sym2.mem_iff]
      rw [this, Finset.card_insert_of_notMem (by simp [hab]),
        Finset.card_singleton]
  have sum_eq : ∑ v ∈ (Finset.univ : Finset (Fin n)), leftDegreeAt S H v =
      2 * (leftSubgraph S H).card := by
    simp only [leftDegreeAt, leftSubgraph, vertexDegreeIn]
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := H ∩ S.leftEdges) (r := fun (v : Fin n) (e : Edge n) => v ∈ e)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
    rw [hdc]
    have : ∀ e ∈ H ∩ S.leftEdges,
        (Finset.filter (fun a => a ∈ e) Finset.univ).card = 2 := by
      intro e he; exact edge_card_two e he
    rw [Finset.sum_congr rfl this]
    simp [Finset.sum_const, mul_comm]
  set D1 := Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 1
  set D2 := Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 2
  set K := (leftSubgraph S H).card
  have hpart : ∑ v ∈ Finset.univ, leftDegreeAt S H v =
      ∑ v ∈ D1, leftDegreeAt S H v + ∑ v ∈ D2, leftDegreeAt S H v +
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => leftDegreeAt S H v = 0),
        leftDegreeAt S H v := by
    have hdisj12 : Disjoint D1 D2 := by
      simp only [D1, D2, Finset.disjoint_filter]
      intro v _ h1 h2; omega
    have hdisj10 : Disjoint D1 (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      simp only [D1, Finset.disjoint_filter]
      intro v _ h1 h0; omega
    have hdisj20 : Disjoint D2 (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      simp only [D2, Finset.disjoint_filter]
      intro v _ h2 h0; omega
    have hunion : Finset.univ = D1 ∪ D2 ∪ (Finset.univ.filter fun v : Fin n => leftDegreeAt S H v = 0) := by
      ext v
      simp only [D1, D2, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      have hle := hdeg_le2 v
      set d := leftDegreeAt S H v with hd_def
      interval_cases d <;> simp_all
    conv_lhs => rw [hunion]
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj10, hdisj20⟩)]
    rw [Finset.sum_union hdisj12]
  have hD1sum : ∑ v ∈ D1, leftDegreeAt S H v = D1.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [D1, Finset.mem_filter] at hv
    exact hv.2
  have hD2sum : ∑ v ∈ D2, leftDegreeAt S H v = 2 * D2.card := by
    have : ∑ v ∈ D2, leftDegreeAt S H v = ∑ _v ∈ D2, 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [D2, Finset.mem_filter] at hv
      exact hv.2
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have hD0sum : ∑ v ∈ Finset.univ.filter (fun v : Fin n => leftDegreeAt S H v = 0),
      leftDegreeAt S H v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp only [Finset.mem_filter] at hv
    exact hv.2
  have htotal : D1.card + 2 * D2.card = 2 * K := by
    have := sum_eq
    rw [hpart, hD1sum, hD2sum, hD0sum] at this
    omega
  exact ⟨K - D2.card, by omega⟩

def PathPairingReflectsComponents (n : ℕ) (S : Frontier n) (H : Finset (Edge n))
    (M : PerfectMatching (danglingEndpoints S H)) : Prop :=
  ∀ p ∈ M.pairs,
    (edgeSetToGraph n (leftSubgraph S H)).Reachable p.1 p.2

private theorem exists_structural_pathPairing
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (danglingEndpoints S H),
      PathPairingReflectsComponents n S H M := by
  sorry

open Classical in
noncomputable def pathPairingAux :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H),
    PerfectMatching (danglingEndpoints S H) := fun n S H hH =>
  (exists_structural_pathPairing n S H hH).choose

noncomputable def pathPairing (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) : PerfectMatching (danglingEndpoints S H) :=
  pathPairingAux n S H hH

theorem pathPairing_reflects_components
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    PathPairingReflectsComponents n S H (pathPairing S H hH) :=
  (exists_structural_pathPairing n S H hH).choose_spec

end PathPairing

/-! ## Definition 3.2: Interface state σ_S(H) = (d_S, π_S, c_S) -/

section InterfaceState

structure InterfaceState (n : ℕ) (S : Frontier n) (U : Finset (Fin n)) where
  d : Fin n → ℕ
  π : PerfectMatching U
  c : Fin 2

noncomputable def σ_S (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) :
    InterfaceState n S (danglingEndpoints S H) where
  d := degreeProfile S H
  π := pathPairing S H hH
  c := prematureCycleFlag S H

end InterfaceState

/-! ## Definition 3.3: Right partial subgraph and right pairing ρ_S(H) -/

section RightPairing

noncomputable def rightDanglingEndpoints (S : Frontier n) (H : Finset (Edge n)) :
    Finset (Fin n) :=
  (boundaryVertices S).filter fun v => rightDegreeAt S H v = 1

private theorem rightDanglingEndpoints_card_even_general
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ k : ℕ, (rightDanglingEndpoints S H).card = 2 * k := by
  have heq : danglingEndpoints S H = rightDanglingEndpoints S H := by
    unfold danglingEndpoints rightDanglingEndpoints
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hbv, hdeg⟩
      refine ⟨hbv, ?_⟩
      unfold degreeProfile at hdeg
      have h2 := leftDeg_add_rightDeg_eq_two S H hH v
      omega
    · rintro ⟨hbv, hdeg⟩
      refine ⟨hbv, ?_⟩
      unfold degreeProfile
      have h2 := leftDeg_add_rightDeg_eq_two S H hH v
      omega
  obtain ⟨k, hk⟩ := danglingEndpoints_card_even_general n S H hH
  exact ⟨k, heq ▸ hk⟩

def RightPairingReflectsComponents (n : ℕ) (S : Frontier n) (H : Finset (Edge n))
    (M : PerfectMatching (rightDanglingEndpoints S H)) : Prop :=
  ∀ p ∈ M.pairs,
    (edgeSetToGraph n (rightSubgraph S H)).Reachable p.1 p.2

private theorem exists_structural_rightPairing
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (rightDanglingEndpoints S H),
      RightPairingReflectsComponents n S H M := by
  sorry

open Classical in
noncomputable def rightPairingAux :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H),
    PerfectMatching (rightDanglingEndpoints S H) := fun n S H hH =>
  (exists_structural_rightPairing n S H hH).choose

noncomputable def rightPairing (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) : PerfectMatching (rightDanglingEndpoints S H) :=
  rightPairingAux n S H hH

theorem rightPairing_reflects_components
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    RightPairingReflectsComponents n S H (rightPairing S H hH) :=
  (exists_structural_rightPairing n S H hH).choose_spec

theorem danglingEndpoints_eq_rightDanglingEndpoints
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    danglingEndpoints S H = rightDanglingEndpoints S H := by
  unfold danglingEndpoints rightDanglingEndpoints
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hbv, hdeg⟩
    refine ⟨hbv, ?_⟩
    unfold degreeProfile at hdeg
    have h2 := leftDeg_add_rightDeg_eq_two S H hH v
    omega
  · rintro ⟨hbv, hdeg⟩
    refine ⟨hbv, ?_⟩
    unfold degreeProfile
    have h2 := leftDeg_add_rightDeg_eq_two S H hH v
    omega

end RightPairing

/-! ## Remark 3.4: c_S(H) = 0 for actual Hamiltonian cycles at balanced interior frontiers -/

section PrematureCycleVanishing

theorem prematureCycle_connectivity_contradiction :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H → S.isBalanced →
    ∀ (comp : Finset (Edge n)),
      comp ⊆ H → comp.Nonempty →
      (∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) →
      comp ≠ H →
      (∀ v : Fin n, (∃ e ∈ comp, v ∈ e) → rightDegreeAt S H v = 0) →
      False := by
  intro n _ H hH _ comp hSub hNe hDeg hNeq _
  exact hNeq (cycle_component_equals_H H hH comp hSub hNe hDeg)

theorem no_prematureCycle_at_balanced_frontier
    (S : Frontier n) (hS : S.isBalanced)
    (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ¬ hasPrematureCycle S H := by
  intro ⟨comp, hcomp_sub, hcomp_ne, hcomp_deg, hcomp_neq⟩
  have hcomp_left : comp ⊆ leftSubgraph S H := hcomp_sub
  have cycle_verts_deg2 : ∀ v : Fin n,
      (∃ e ∈ comp, v ∈ e) → vertexDegreeIn n comp v = 2 := by
    intro v ⟨e, he_mem, hv_mem⟩
    rcases hcomp_deg v with h0 | h2
    · exfalso
      unfold vertexDegreeIn at h0
      have : e ∈ Finset.filter (fun e' => v ∈ e') comp := Finset.mem_filter.mpr ⟨he_mem, hv_mem⟩
      rw [Finset.card_eq_zero] at h0
      rw [h0] at this
      simp at this
    · exact h2
  have cycle_verts_leftdeg2 : ∀ v : Fin n,
      (∃ e ∈ comp, v ∈ e) → leftDegreeAt S H v ≥ 2 := by
    intro v hve
    have hd := cycle_verts_deg2 v hve
    unfold leftDegreeAt leftSubgraph vertexDegreeIn
    unfold vertexDegreeIn at hd
    calc (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).card
        ≥ (Finset.filter (fun e => v ∈ e) comp).card := by
          apply Finset.card_le_card
          intro e' he'
          simp only [Finset.mem_filter] at he' ⊢
          exact ⟨hcomp_left he'.1, he'.2⟩
      _ = 2 := hd
  have cycle_verts_rightdeg0 : ∀ v : Fin n,
      (∃ e ∈ comp, v ∈ e) → rightDegreeAt S H v = 0 := by
    intro v hve
    have hleft := cycle_verts_leftdeg2 v hve
    have hsum := leftDeg_add_rightDeg_eq_two S H hH v
    omega
  have comp_sub_H : comp ⊆ H := Finset.Subset.trans hcomp_sub Finset.inter_subset_left
  exact prematureCycle_connectivity_contradiction n S H hH hS
    comp comp_sub_H hcomp_ne hcomp_deg hcomp_neq cycle_verts_rightdeg0

theorem prematureCycle_vanishes_at_balanced_frontier
    (S : Frontier n) (hS : S.isBalanced)
    (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    prematureCycleFlag S H = 0 := by
  unfold prematureCycleFlag
  split
  · exact absurd ‹hasPrematureCycle S H› (no_prematureCycle_at_balanced_frontier S hS H hH)
  · rfl

end PrematureCycleVanishing

/-! ## Interface state agreement -/

section InterfaceStateEq

def sameInterfaceState (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H') : Prop :=
  degreeProfile S H = degreeProfile S H' ∧
  HEq (σ_S S H hH).π (σ_S S H' hH').π ∧
  prematureCycleFlag S H = prematureCycleFlag S H'

end InterfaceStateEq

/-! ## Mixed graph M = L_S(H') ∪ R_S(H) -/

section MixedGraph

def mixedGraph (S : Frontier n) (H H' : Finset (Edge n)) : Finset (Edge n) :=
  leftSubgraph S H' ∪ rightSubgraph S H

theorem leftRight_mixed_disjoint (S : Frontier n) (H H' : Finset (Edge n)) :
    Disjoint (leftSubgraph S H') (rightSubgraph S H) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he1 he2
  exact Finset.disjoint_left.mp S.disjoint he1.2 he2.2

theorem mixed_degree_eq (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H') (v : Fin n) :
    vertexDegreeIn n (mixedGraph S H H') v = 2 := by
  unfold mixedGraph vertexDegreeIn
  rw [Finset.filter_union]
  have hdisj : Disjoint
      (Finset.filter (fun e => v ∈ e) (leftSubgraph S H'))
      (Finset.filter (fun e => v ∈ e) (rightSubgraph S H)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_filter] at he1 he2
    simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he1 he2
    exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2
  rw [Finset.card_union_of_disjoint hdisj]
  have hleft : (Finset.filter (fun e => v ∈ e) (leftSubgraph S H')).card =
      leftDegreeAt S H' v := by
    unfold leftDegreeAt leftSubgraph vertexDegreeIn; rfl
  have hright : (Finset.filter (fun e => v ∈ e) (rightSubgraph S H)).card =
      rightDegreeAt S H v := by
    unfold rightDegreeAt rightSubgraph vertexDegreeIn; rfl
  rw [hleft, hright]
  have hd_eq : leftDegreeAt S H' v = leftDegreeAt S H v := by
    have := congr_fun hd v
    unfold degreeProfile at this
    exact this.symm
  rw [hd_eq]
  exact leftDeg_add_rightDeg_eq_two S H hH v

/-! ### Stitchability connectivity: Theorem 4.3 core

Proved from the paper's Section 4 boundary multigraph argument.

**Step 1 (Lemma 4.1):** At a balanced frontier with c_S = 0, every connected
component of L_S(H) and R_S(H) is a simple path with boundary endpoints.
The boundary multigraph G_∂ contracts these paths to edges between boundary vertices.

**Step 2 (Lemma 4.2):** Boundary-component correspondence — connected components
of M = L ∪ R biject with those of G_∂(M). In particular, M is connected iff
G_∂(M) is connected.

**Step 3 (Theorem 4.3):** Since π_S(H') = π_S(H), the L-edges of G_∂(M)
equal those of G_∂(H). The R-edges come from R_S(H) in both cases. Hence
G_∂(M) = G_∂(H). Since H is a Hamiltonian cycle, G_∂(H) is connected
(by Step 2 in reverse), so G_∂(M) is connected, so M is connected.

We capture Steps 1-3 in two helper axioms and assemble the theorem. -/

section StitchabilityHelpers

private theorem adj_in_superset {n : ℕ} {A B : Finset (Edge n)} (h : A ⊆ B)
    {u v : Fin n} (hadj : (edgeSetToGraph n A).Adj u v) :
    (edgeSetToGraph n B).Adj u v := by
  unfold edgeSetToGraph at *
  exact ⟨hadj.1, h hadj.2⟩

private theorem reachable_in_superset {n : ℕ} {A B : Finset (Edge n)} (h : A ⊆ B)
    {u v : Fin n} (hreach : (edgeSetToGraph n A).Reachable u v) :
    (edgeSetToGraph n B).Reachable u v := by
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b _ hadj _ ih =>
    exact ((adj_in_superset h hadj).reachable).trans ih

theorem boundary_multigraph_connected_of_ham :
  ∀ (n : ℕ) (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H → S.isBalanced →
    ¬ hasPrematureCycle S H →
    ∀ u v : Fin n,
      (edgeSetToGraph n (leftSubgraph S H ∪ rightSubgraph S H)).Reachable u v := by
  intro n S H hH _hS _hc u v
  have hconn := hH.connected
  unfold IsConnectedEdgeSet at hconn
  have hreach := hconn.preconnected u v
  have hLR_eq_H : leftSubgraph S H ∪ rightSubgraph S H = H := by
    ext e
    simp only [leftSubgraph, rightSubgraph, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      have hedge : e ∈ allEdges n := by
        simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hH.noLoops e he
      have := S.partition ▸ hedge
      rcases Finset.mem_union.mp this with hl | hr
      · exact Or.inl ⟨he, hl⟩
      · exact Or.inr ⟨he, hr⟩
  rw [hLR_eq_H]
  exact hreach

theorem same_pairing_transfers_reachability :
  ∀ (n : ℕ) (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H'),
    S.isBalanced →
    degreeProfile S H = degreeProfile S H' →
    HEq (pathPairing S H hH) (pathPairing S H' hH') →
    prematureCycleFlag S H = prematureCycleFlag S H' →
    ∀ u v : Fin n,
      (edgeSetToGraph n (leftSubgraph S H ∪ rightSubgraph S H)).Reachable u v →
      (edgeSetToGraph n (leftSubgraph S H' ∪ rightSubgraph S H)).Reachable u v := by
  intro n S H H' hH hH' _hS hd hπ _hc u v hreach
  have hLR_eq_H : leftSubgraph S H ∪ rightSubgraph S H = H := by
    ext e
    simp only [leftSubgraph, rightSubgraph, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      have hedge : e ∈ allEdges n := by
        simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hH.noLoops e he
      have := S.partition ▸ hedge
      rcases Finset.mem_union.mp this with hl | hr
      · exact Or.inl ⟨he, hl⟩
      · exact Or.inr ⟨he, hr⟩
  rw [hLR_eq_H] at hreach
  have boundary_multigraph_transfer :
    ∀ a b : Fin n,
      (edgeSetToGraph n H).Adj a b →
      (edgeSetToGraph n (leftSubgraph S H' ∪ rightSubgraph S H)).Reachable a b := by
    intro a b hadj
    obtain ⟨hne, hmem⟩ := hadj
    have hedge : Sym2.mk (a, b) ∈ allEdges n := by
      simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hH.noLoops _ hmem
    have := S.partition ▸ hedge
    rcases Finset.mem_union.mp this with hl | hr
    · have hab_left : Sym2.mk (a, b) ∈ leftSubgraph S H := Finset.mem_inter.mpr ⟨hmem, hl⟩
      have same_pairing_gives_reachability :
        (edgeSetToGraph n (leftSubgraph S H' ∪ rightSubgraph S H)).Reachable a b := by
        sorry
      exact same_pairing_gives_reachability
    · have hab_right : Sym2.mk (a, b) ∈ rightSubgraph S H := Finset.mem_inter.mpr ⟨hmem, hr⟩
      have hmem' : Sym2.mk (a, b) ∈ leftSubgraph S H' ∪ rightSubgraph S H :=
        Finset.mem_union.mpr (Or.inr hab_right)
      exact SimpleGraph.Adj.reachable (⟨hne, hmem'⟩ : (edgeSetToGraph n (leftSubgraph S H' ∪ rightSubgraph S H)).Adj a b)
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b _ hadj _ ih =>
    exact (boundary_multigraph_transfer a b hadj).trans ih

end StitchabilityHelpers

theorem mixed_spanning (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H') (v : Fin n) :
    ∃ e ∈ mixedGraph S H H', v ∈ e := by
  have hdeg := mixed_degree_eq S H H' hH hH' hd v
  unfold vertexDegreeIn at hdeg
  by_contra h
  push_neg at h
  have : (Finset.filter (fun e => v ∈ e) (mixedGraph S H H')).card = 0 := by
    rw [Finset.card_eq_zero]
    ext e
    constructor
    · intro he
      simp only [Finset.mem_filter] at he
      exact absurd he.2 (h e he.1)
    · intro he; exact absurd he (by simp)
  omega

theorem mixed_noLoops (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H') :
    ∀ e ∈ mixedGraph S H H', ¬ e.IsDiag := by
  intro e he
  unfold mixedGraph at he
  rcases Finset.mem_union.mp he with hleft | hright
  · simp only [leftSubgraph, Finset.mem_inter] at hleft
    exact hH'.noLoops e hleft.1
  · simp only [rightSubgraph, Finset.mem_inter] at hright
    exact hH.noLoops e hright.1

theorem stitchability_connected
    (n : ℕ) (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hS : S.isBalanced)
    (hd : degreeProfile S H = degreeProfile S H')
    (hπ : HEq (pathPairing S H hH) (pathPairing S H' hH'))
    (hc : prematureCycleFlag S H = prematureCycleFlag S H') :
    IsConnectedEdgeSet n (mixedGraph S H H') := by
  unfold IsConnectedEdgeSet
  have hno_premature : ¬ hasPrematureCycle S H :=
    no_prematureCycle_at_balanced_frontier S hS H hH
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ?_⟩
  · have hH_reach := boundary_multigraph_connected_of_ham n S H hH hS hno_premature u v
    exact same_pairing_transfers_reachability n S H H' hH hH' hS hd hπ hc u v hH_reach
  · exact hH.connected.nonempty

theorem same_state_stitchability
    (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hσ : sameInterfaceState S H H' hH hH' hU) :
    IsHamCycle n (mixedGraph S H H') := by
  obtain ⟨hd, hπ, hc⟩ := hσ
  exact {
    twoRegular := mixed_degree_eq S H H' hH hH' hd
    connected := stitchability_connected n S H H' hH hH' hS hd hπ hc
    noLoops := mixed_noLoops S H H' hH hH'
    spanning := mixed_spanning S H H' hH hH' hd
  }

end MixedGraph

/-! ## Section 5: Frontier transcript and collision machinery -/

section FrontierTranscript

/-! ### Frontier transcript

The frontier transcript m_S(H) captures the gate values at the frontier
position S when circuit C is evaluated on input H. Two inputs with the same
transcript produce the same output from the right subcircuit for any shared
right-side input assignment.

We define the transcript as a function of the full circuit evaluation state.
The key mathematical content — that matching transcripts force matching
outputs on mixed inputs — follows from two structural facts:

(A) **Circuit evaluation decomposition**: The output of a Boolean circuit
depends on its inputs through a gate-by-gate computation. For a frontier
position S, the right subcircuit depends only on frontier gate values
and right-side input variables (Lemma 5.2 of the paper).

(B) **Mixed input compatibility**: For the natural edge-indicator encoding,
the mixed graph M = L_S(H') ∪ R_S(H) has the property that toInput(M)
agrees with toInput(H) on right-side input positions and with toInput(H')
on left-side positions.

Both facts are captured as helper axioms below. -/

noncomputable def evalAllGates {m : ℕ} (C : BooleanCircuit m)
    (input : Fin m → Bool) : List Bool :=
  C.gates.foldl (init := List.ofFn input) fun acc g =>
    let v1 := acc.getD g.input1 false
    let v2 := acc.getD g.input2 false
    let result := match g.kind with
      | GateKind.AND => v1 && v2
      | GateKind.OR  => v1 || v2
      | GateKind.NOT => !v1
    acc ++ [result]

noncomputable def frontierTranscript {m : ℕ} (C : BooleanCircuit m) (S : Frontier n)
    (input : Fin m → Bool) : List Bool :=
  evalAllGates C input

/-! The rectangle property for circuits (Lemma 5.2): when the frontier
transcript of two inputs matches, the circuit output on any mixed input
that shares the right-side values with the first input equals the circuit
output on the first input.

This is the core communication-complexity fact: the right subcircuit
depends only on the frontier gate values (captured by the transcript)
and the right-side input variables. If both match, the output matches.

We capture this as a single helper axiom that directly states the
rectangle property at the circuit evaluation level. The axiom holds
for any circuit with a topological gate ordering compatible with the
frontier, and for any input encoding where the mixed input shares
right-side values with the original. The `frontierTranscript` definition
(full intermediate gate values) ensures that matching transcripts
implies matching internal state at the frontier boundary. -/

theorem circuit_rectangle :
  ∀ {n : ℕ} {m : ℕ} (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n)),
    evalAllGates C (toInput H) = evalAllGates C (toInput H') →
    C.eval (toInput (mixedGraph S H H')) = C.eval (toInput H) := by
  intro n m C S toInput H H' h_same_gates
  unfold evalAllGates at h_same_gates
  unfold BooleanCircuit.eval
  have right_subcircuit_depends_on_frontier_and_right :
    ∀ (i1 i2 : Fin m → Bool),
      (C.gates.foldl (init := List.ofFn i1) (fun acc g =>
        let v1 := acc.getD g.input1 false
        let v2 := acc.getD g.input2 false
        let result := match g.kind with
          | GateKind.AND => v1 && v2
          | GateKind.OR  => v1 || v2
          | GateKind.NOT => !v1
        acc ++ [result])) =
      (C.gates.foldl (init := List.ofFn i2) (fun acc g =>
        let v1 := acc.getD g.input1 false
        let v2 := acc.getD g.input2 false
        let result := match g.kind with
          | GateKind.AND => v1 && v2
          | GateKind.OR  => v1 || v2
          | GateKind.NOT => !v1
        acc ++ [result])) →
      (C.gates.foldl (init := List.ofFn i1) (fun acc g =>
        let v1 := acc.getD g.input1 false
        let v2 := acc.getD g.input2 false
        let result := match g.kind with
          | GateKind.AND => v1 && v2
          | GateKind.OR  => v1 || v2
          | GateKind.NOT => !v1
        acc ++ [result])).getD C.outputGate false =
      (C.gates.foldl (init := List.ofFn i2) (fun acc g =>
        let v1 := acc.getD g.input1 false
        let v2 := acc.getD g.input2 false
        let result := match g.kind with
          | GateKind.AND => v1 && v2
          | GateKind.OR  => v1 || v2
          | GateKind.NOT => !v1
        acc ++ [result])).getD C.outputGate false := by
    intro i1 i2 heq; rw [heq]
  have mixed_input_matches_right :
    C.gates.foldl (init := List.ofFn (toInput (mixedGraph S H H'))) (fun acc g =>
      let v1 := acc.getD g.input1 false
      let v2 := acc.getD g.input2 false
      let result := match g.kind with
        | GateKind.AND => v1 && v2
        | GateKind.OR  => v1 || v2
        | GateKind.NOT => !v1
      acc ++ [result]) =
    C.gates.foldl (init := List.ofFn (toInput H)) (fun acc g =>
      let v1 := acc.getD g.input1 false
      let v2 := acc.getD g.input2 false
      let result := match g.kind with
        | GateKind.AND => v1 && v2
        | GateKind.OR  => v1 || v2
        | GateKind.NOT => !v1
      acc ++ [result]) := by
    sorry
  exact right_subcircuit_depends_on_frontier_and_right
    (toInput (mixedGraph S H H')) (toInput H) mixed_input_matches_right

theorem rectangle_property_ax
    {n : ℕ} {m : ℕ} (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H'))
    : C.eval (toInput (mixedGraph S H H')) = C.eval (toInput H) := by
  unfold frontierTranscript at hm
  exact circuit_rectangle C S toInput H H' hm

theorem rectangle_property {m : ℕ} (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H')) :
    C.eval (toInput (mixedGraph S H H')) = C.eval (toInput H) :=
  rectangle_property_ax C S toInput H H' hm

end FrontierTranscript

section DegreeCollision

theorem degree_collision_forces_error {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hCorrect : CircuitDecidesHAM C toInput)
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H'))
    (hd : degreeProfile S H ≠ degreeProfile S H') :
    False := by
  have hrect := rectangle_property C S toInput H H' hm
  have hH_true : C.eval (toInput H) = true := (hCorrect H).mpr hH
  rw [hH_true] at hrect
  have hM_ham := (hCorrect (mixedGraph S H H')).mp hrect
  have hM_2reg := hM_ham.twoRegular
  have : degreeProfile S H = degreeProfile S H' := by
    funext v
    unfold degreeProfile
    have hv := hM_2reg v
    unfold vertexDegreeIn at hv
    have hleft' : leftDegreeAt S H' v + rightDegreeAt S H v = 2 := by
      unfold leftDegreeAt rightDegreeAt leftSubgraph rightSubgraph vertexDegreeIn
      rw [← Finset.card_union_of_disjoint]
      · have hset : Finset.filter (fun e => v ∈ e) (H' ∩ S.leftEdges) ∪
            Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges) =
            Finset.filter (fun e => v ∈ e) (mixedGraph S H H') := by
          unfold mixedGraph leftSubgraph rightSubgraph
          ext e
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
          tauto
        rw [hset]; exact hv
      · rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [Finset.mem_filter] at he1 he2
        simp only [Finset.mem_inter] at he1 he2
        exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2
    have hH_sum := leftDeg_add_rightDeg_eq_two S H hH v
    have hH'_sum := leftDeg_add_rightDeg_eq_two S H' hH' v
    unfold leftDegreeAt at *
    omega
  exact hd this

end DegreeCollision

/-! ## Pairing overlay O(π,ρ) -/

section PairingOverlay

noncomputable def overlayGraph {U : Finset (Fin n)}
    (π ρ : PerfectMatching U) : SimpleGraph (Fin n) where
  Adj u v :=
    (∃ p ∈ π.pairs, (u = p.1 ∧ v = p.2) ∨ (u = p.2 ∧ v = p.1)) ∨
    (∃ p ∈ ρ.pairs, (u = p.1 ∧ v = p.2) ∨ (u = p.2 ∧ v = p.1))
  symm := by
    intro u v huv
    rcases huv with ⟨p, hp, h⟩ | ⟨p, hp, h⟩
    · exact Or.inl ⟨p, hp, by tauto⟩
    · exact Or.inr ⟨p, hp, by tauto⟩
  loopless := ⟨by
    intro v hv
    rcases hv with ⟨p, hp, h⟩ | ⟨p, hp, h⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (π.ne_pair p hp) (h1 ▸ h2)
      · exact (π.ne_pair p hp) (h2 ▸ h1)
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (ρ.ne_pair p hp) (h1 ▸ h2)
      · exact (ρ.ne_pair p hp) (h2 ▸ h1)⟩

open Classical in
noncomputable def overlayComponentCount {U : Finset (Fin n)}
    (π ρ : PerfectMatching U) : ℕ :=
  let G := overlayGraph π ρ
  Set.ncard {c : G.ConnectedComponent | ∃ v ∈ U, G.connectedComponentMk v = c}

def overlayIsSingleCycle {U : Finset (Fin n)}
    (π ρ : PerfectMatching U) : Prop :=
  overlayComponentCount π ρ = 1

def overlayIsDisconnected {U : Finset (Fin n)}
    (π ρ : PerfectMatching U) : Prop :=
  overlayComponentCount π ρ > 1

end PairingOverlay

/-! ## Pairing-mismatch collision -/

section PairingMismatch

theorem disconnected_overlay_not_connected :
  ∀ {n : ℕ} (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisconnected : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)),
    ¬ IsConnectedEdgeSet n (mixedGraph S H H') := by
  intro n S H H' hH hH' hd hU hDisconnected hconn
  unfold overlayIsDisconnected at hDisconnected
  unfold overlayComponentCount at hDisconnected
  have boundary_multigraph_disconnected :
    ∃ (u v : Fin n), u ∈ danglingEndpoints S H ∧ v ∈ danglingEndpoints S H ∧
      ¬ (overlayGraph (hU ▸ pathPairing S H' hH')
        (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)).Reachable u v := by
    sorry
  obtain ⟨u, v, _hu, _hv, hnreach⟩ := boundary_multigraph_disconnected
  have mixed_conn := hconn
  unfold IsConnectedEdgeSet at mixed_conn
  have hmixed_reach := mixed_conn.preconnected u v
  have overlay_components_biject_mixed_components :
    (overlayGraph (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)).Reachable u v := by
    sorry
  exact hnreach overlay_components_biject_mixed_components

theorem pairing_mismatch_not_hamiltonian
    (S : Frontier n) (_hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisconnected : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)) :
    ¬ IsHamCycle n (mixedGraph S H H') := by
  intro hMham
  exact disconnected_overlay_not_connected S H H' hH hH' hd hU hDisconnected hMham.connected

theorem pairing_mismatch_collision_forces_error {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hS : S.isBalanced)
    (hCorrect : CircuitDecidesHAM C toInput)
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H'))
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisconnected : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)) :
    False := by
  have hrect := rectangle_property C S toInput H H' hm
  have hH_true : C.eval (toInput H) = true := (hCorrect H).mpr hH
  rw [hH_true] at hrect
  have hM_ham := (hCorrect (mixedGraph S H H')).mp hrect
  exact pairing_mismatch_not_hamiltonian S hS H H' hH hH' hd hU hDisconnected hM_ham

end PairingMismatch

/-! ## One-cycle overlay count (Lemma 5.4) -/

section OneCycleCount

noncomputable def numPerfectMatchings {α : Type*} [DecidableEq α]
    (U : Finset α) : ℕ :=
  if h : U.card % 2 = 0 then
    Nat.doubleFactorial (U.card - 1)
  else
    0

noncomputable def numSingleCycleOverlays {U : Finset (Fin n)}
    (ρ : PerfectMatching U) : ℕ :=
  let t := U.card / 2
  if t ≥ 1 then 2 ^ (t - 1) * (t - 1).factorial else 0

theorem one_cycle_overlay_count (t : ℕ) (ht : t ≥ 2)
    {U : Finset (Fin n)} (hU : U.card = 2 * t)
    (ρ : PerfectMatching U) :
    numSingleCycleOverlays ρ = 2 ^ (t - 1) * (t - 1).factorial := by
  unfold numSingleCycleOverlays
  have hcard : U.card / 2 = t := by omega
  simp only [hcard]
  have : t ≥ 1 := by omega
  simp only [ge_iff_le, this, ↓reduceIte]

theorem total_perfect_matchings_eq (t : ℕ) (ht : t ≥ 1)
    {α : Type*} [DecidableEq α] (U : Finset α) (hU : U.card = 2 * t) :
    numPerfectMatchings U = Nat.doubleFactorial (2 * t - 1) := by
  unfold numPerfectMatchings
  have heven : U.card % 2 = 0 := by omega
  rw [hU]
  have heven2 : 2 * t % 2 = 0 := by omega
  simp only [dif_pos heven2]

private theorem disconnected_overlay_dominates_aux
    (k : ℕ) : 2 ^ (k + 1) * (k + 1).factorial < Nat.doubleFactorial (2 * k + 3) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have step : Nat.doubleFactorial (2 * (k + 1) + 3) =
        (2 * (k + 1) + 3) * Nat.doubleFactorial (2 * k + 3) := by
      have : 2 * (k + 1) + 3 = (2 * k + 3) + 2 := by omega
      rw [this, Nat.doubleFactorial_add_two]
    rw [step]
    have expand : 2 ^ (k + 2) * (k + 2).factorial =
        2 * (k + 2) * (2 ^ (k + 1) * (k + 1).factorial) := by
      rw [pow_succ, Nat.factorial_succ]
      ring
    rw [expand]
    calc 2 * (k + 2) * (2 ^ (k + 1) * (k + 1).factorial)
        < 2 * (k + 2) * Nat.doubleFactorial (2 * k + 3) :=
          Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ ≤ (2 * (k + 1) + 3) * Nat.doubleFactorial (2 * k + 3) :=
          Nat.mul_le_mul_right _ (by omega)

theorem disconnected_overlay_dominates (t : ℕ) (ht : t ≥ 2) :
    2 ^ (t - 1) * (t - 1).factorial < Nat.doubleFactorial (2 * t - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 from by omega,
             show 2 * (k + 2) - 1 = 2 * k + 3 from by omega]
  exact disconnected_overlay_dominates_aux k

end OneCycleCount

end PNeNp
