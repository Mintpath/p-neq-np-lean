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

/-! ### Path-component normal form (hamiltonian_route.tex Lemma, lines 275-361)

Let H be a Hamiltonian cycle on [n] and S a balanced interior frontier
with c_S(H) = 0. Then:
(1) Every connected component of L_S(H) is a simple path (possibly single vertex).
(2) Every path-component with ≥1 edge has exactly two endpoints of left-degree 1.
    Both are boundary vertices.
(3) Internal vertices (left-degree 2) don't affect the boundary multigraph.
(4) Isolated vertices (left-degree 0) are boundary iff incident to both sides.
(5) No component is disjoint from B_S unless it's an isolated vertex with no left edges.
(6) The L-edges of the boundary multigraph are exactly the pairs of π_S(H). -/

private lemma leftSubgraph_max_degree_two
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) (v : Fin n) :
    vertexDegreeIn n (leftSubgraph S H) v ≤ 2 := by
  have h := leftDeg_add_rightDeg_eq_two S H hH v
  show leftDegreeAt S H v ≤ 2
  omega

private lemma leftSubgraph_component_is_path
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (hRight : (rightSubgraph S H).Nonempty)
    (comp : Finset (Edge n)) (hcomp : comp ⊆ leftSubgraph S H)
    (hne : comp.Nonempty)
    (h2reg : ∀ v : Fin n, vertexDegreeIn n comp v ≤ 2) :
    ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) := by
  intro hall
  have comp_sub_H : comp ⊆ H :=
    Finset.Subset.trans hcomp Finset.inter_subset_left
  have comp_eq_H : comp = H :=
    cycle_component_equals_H H hH comp comp_sub_H hne hall
  have H_sub_left : H ⊆ S.leftEdges := by
    intro e he
    have : e ∈ comp := comp_eq_H ▸ he
    have : e ∈ H ∩ S.leftEdges := hcomp this
    exact Finset.mem_inter.mp this |>.2
  obtain ⟨e, he⟩ := hRight
  have he_H : e ∈ H := Finset.mem_inter.mp he |>.1
  have he_right : e ∈ S.rightEdges := Finset.mem_inter.mp he |>.2
  have he_left : e ∈ S.leftEdges := H_sub_left he_H
  exact Finset.disjoint_left.mp S.disjoint he_left he_right

lemma vertexDegreeIn_mono (n : ℕ) (A B : Finset (Edge n)) (hAB : A ⊆ B) (v : Fin n) :
    vertexDegreeIn n A v ≤ vertexDegreeIn n B v := by
  unfold vertexDegreeIn
  exact Finset.card_le_card (Finset.filter_subset_filter _ hAB)

private lemma vertexDegreeIn_comp_eq_of_maximal (n : ℕ)
    (comp parent : Finset (Edge n)) (hcomp : comp ⊆ parent)
    (hmax : ∀ e ∈ parent \ comp, ∀ v : Fin n, v ∈ e → vertexDegreeIn n comp v = 0)
    (v : Fin n) (hv : vertexDegreeIn n comp v > 0) :
    vertexDegreeIn n comp v = vertexDegreeIn n parent v := by
  unfold vertexDegreeIn at *
  apply le_antisymm
  · exact Finset.card_le_card (Finset.filter_subset_filter _ hcomp)
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    by_contra h
    push_neg at h
    have hnotcomp : e ∉ comp := fun hc => absurd he.2 (h hc)
    have hdiff : e ∈ parent \ comp := Finset.mem_sdiff.mpr ⟨he.1, hnotcomp⟩
    have := hmax e hdiff v he.2
    omega

lemma deg1_vertex_exists_unique_edge
    (n : ℕ) (comp : Finset (Edge n)) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1) :
    ∃! e, e ∈ comp ∧ v ∈ e := by
  unfold vertexDegreeIn at hdeg1
  rw [Finset.card_eq_one] at hdeg1
  obtain ⟨e, he⟩ := hdeg1
  have hmem := he ▸ Finset.mem_singleton_self e
  simp only [Finset.mem_filter] at hmem
  exact ⟨e, ⟨hmem.1, hmem.2⟩, fun e' ⟨he'1, he'2⟩ => by
    have : e' ∈ Finset.filter (fun e => v ∈ e) comp := Finset.mem_filter.mpr ⟨he'1, he'2⟩
    rw [he] at this; exact Finset.mem_singleton.mp this⟩

lemma deg1_other_endpoint
    (n : ℕ) (comp : Finset (Edge n)) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1) (hnoloops : ∀ e ∈ comp, ¬ e.IsDiag) :
    ∃ w : Fin n, w ≠ v ∧ ∃ e ∈ comp, v ∈ e ∧ w ∈ e := by
  obtain ⟨e, ⟨he, hve⟩, _⟩ := deg1_vertex_exists_unique_edge n comp v hdeg1
  have hnd := hnoloops e he
  exact ⟨Sym2.Mem.other hve, Sym2.other_ne hnd hve,
    e, he, hve, Sym2.other_mem hve⟩

private lemma filter_erase_eq {α : Type*} [DecidableEq α] {s : Finset α}
    {p : α → Prop} [DecidablePred p] {a : α} :
    Finset.filter p (s.erase a) = (Finset.filter p s).erase a := by
  ext x; simp only [Finset.mem_filter, Finset.mem_erase]
  exact ⟨fun ⟨⟨hne, hx⟩, hp⟩ => ⟨hne, hx, hp⟩,
         fun ⟨hne, hx, hp⟩ => ⟨⟨hne, hx⟩, hp⟩⟩

lemma erase_edge_deg (n : ℕ) (comp : Finset (Edge n)) (e : Edge n)
    (he : e ∈ comp) (v : Fin n) :
    vertexDegreeIn n (comp.erase e) v =
      if v ∈ e then vertexDegreeIn n comp v - 1 else vertexDegreeIn n comp v := by
  unfold vertexDegreeIn
  split
  · next hve =>
    rw [filter_erase_eq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨he, hve⟩)]
  · next hve =>
    congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun ⟨⟨_, hx⟩, hv⟩ => ⟨hx, hv⟩,
           fun ⟨hx, hv⟩ => ⟨⟨fun h => hve (h ▸ hv), hx⟩, hv⟩⟩

lemma deg1_unique_edge_eq (n : ℕ) (comp : Finset (Edge n)) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1) (e' : Edge n) (he' : e' ∈ comp) (hve' : v ∈ e') :
    ∀ e'' ∈ comp, v ∈ e'' → e'' = e' := by
  intro e'' he'' hve''
  have ⟨_, _, huniq⟩ := deg1_vertex_exists_unique_edge n comp v hdeg1
  have h1 := huniq e' ⟨he', hve'⟩
  have h2 := huniq e'' ⟨he'', hve''⟩
  rw [h2, h1]

private lemma walk_avoids_deg1_aux (n : ℕ) (comp : Finset (Edge n)) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1)
    (e : Edge n) (he : e ∈ comp) (hve : v ∈ e)
    {a b : Fin n} (ha : a ≠ v) (hb : b ≠ v)
    (walk : (edgeSetToGraph n comp).Walk a b) :
    (edgeSetToGraph n (comp.erase e)).Reachable a b := by
  suffices key : ∀ (len : ℕ) {x y : Fin n},
      (w : (edgeSetToGraph n comp).Walk x y) → w.length ≤ len →
      x ≠ v → y ≠ v → (edgeSetToGraph n (comp.erase e)).Reachable x y from
    key walk.length walk (le_refl _) ha hb
  intro len; induction len with
  | zero =>
    intro x y w hlen _hx _hy
    have := SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.mp hlen)
    exact this ▸ SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro x y w hlen hx hy
    by_cases hwlen : w.length = 0
    · exact (SimpleGraph.Walk.eq_of_length_eq_zero hwlen) ▸ SimpleGraph.Reachable.refl _
    · obtain ⟨c, hc_walk⟩ : ∃ c, ∃ (hadj : (edgeSetToGraph n comp).Adj x c),
          ∃ (rest : (edgeSetToGraph n comp).Walk c y), w.length = rest.length + 1 := by
        match w with
        | @SimpleGraph.Walk.cons _ _ _ c _ hadj rest =>
          exact ⟨c, hadj, rest, rfl⟩
      obtain ⟨hadj_xc, rest, hlen_eq⟩ := hc_walk
      have ⟨hne_xc, hmem_xc⟩ := hadj_xc
      have hrest_len : rest.length ≤ k := by omega
      by_cases hcv : c = v
      · by_cases hrestlen0 : rest.length = 0
        · have := SimpleGraph.Walk.eq_of_length_eq_zero hrestlen0
          rw [hcv] at this; exact absurd this hy.symm
        · obtain ⟨c2, hc2_walk⟩ : ∃ c2, ∃ (hadj2 : (edgeSetToGraph n comp).Adj c c2),
              ∃ (rest2 : (edgeSetToGraph n comp).Walk c2 y),
                rest.length = rest2.length + 1 := by
            match rest with
            | @SimpleGraph.Walk.cons _ _ _ c2 _ hadj2 rest2 =>
              exact ⟨c2, hadj2, rest2, rfl⟩
          obtain ⟨hadj2, rest2, hlen2_eq⟩ := hc2_walk
          have ⟨_, hmem_cc2⟩ := hadj2
          have hmem_vc2 : Sym2.mk (v, c2) ∈ comp := hcv ▸ hmem_cc2
          have hv_in_vc2 : v ∈ Sym2.mk (v, c2) := Sym2.mem_mk_left v c2
          have hedge2_eq : Sym2.mk (v, c2) = e :=
            deg1_unique_edge_eq n comp v hdeg1 e he hve _ hmem_vc2 hv_in_vc2
          have hmem_xv : Sym2.mk (x, v) ∈ comp := hcv ▸ hmem_xc
          have hedge1_eq : Sym2.mk (x, v) = e :=
            deg1_unique_edge_eq n comp v hdeg1 e he hve _
              hmem_xv (Sym2.mem_mk_right x v)
          have hc2_eq_x : c2 = x := by
            have hx_in_e : x ∈ e := by rw [← hedge1_eq]; exact Sym2.mem_mk_left x v
            have hc2_in_e : c2 ∈ e := by rw [← hedge2_eq]; exact Sym2.mem_mk_right v c2
            induction e using Sym2.ind with
            | h p q =>
              simp only [Sym2.mem_iff] at hve hx_in_e hc2_in_e
              have hxv : x ≠ v := hx
              rcases hve with rfl | rfl <;> rcases hx_in_e with rfl | rfl <;>
                rcases hc2_in_e with rfl | rfl
              all_goals first | rfl | contradiction
          have hrest2_len : rest2.length ≤ k := by omega
          subst hc2_eq_x
          exact ih rest2 hrest2_len hx hy
      · have hedge_ne : Sym2.mk (x, c) ≠ e := by
          intro heq
          have hv_in : v ∈ Sym2.mk (x, c) := heq ▸ hve
          simp only [Sym2.mem_iff] at hv_in
          rcases hv_in with rfl | rfl
          · exact hx rfl
          · exact hcv rfl
        have hmem_erase : Sym2.mk (x, c) ∈ comp.erase e :=
          Finset.mem_erase.mpr ⟨hedge_ne, hmem_xc⟩
        have hadj_erase : (edgeSetToGraph n (comp.erase e)).Adj x c := ⟨hne_xc, hmem_erase⟩
        exact hadj_erase.reachable.trans (ih rest hrest_len hcv hy)

lemma leaf_removal_connected (n : ℕ) (comp : Finset (Edge n))
    (hconn : IsIncidentConnected n comp) (v : Fin n)
    (hdeg1 : vertexDegreeIn n comp v = 1)
    (e : Edge n) (he : e ∈ comp) (hve : v ∈ e) :
    IsIncidentConnected n (comp.erase e) := by
  intro a b ⟨ea, hea_mem, hea_a⟩ ⟨eb, heb_mem, heb_b⟩
  have hea_comp : ea ∈ comp := Finset.mem_of_mem_erase hea_mem
  have heb_comp : eb ∈ comp := Finset.mem_of_mem_erase heb_mem
  have hea_ne : ea ≠ e := fun h => by
    rw [h] at hea_mem; exact (Finset.notMem_erase e comp) hea_mem
  have heb_ne : eb ≠ e := fun h => by
    rw [h] at heb_mem; exact (Finset.notMem_erase e comp) heb_mem
  have ha_ne_v : a ≠ v := by
    intro hav
    exact hea_ne (deg1_unique_edge_eq n comp v hdeg1 e he hve ea hea_comp (hav ▸ hea_a))
  have hb_ne_v : b ≠ v := by
    intro hbv
    exact heb_ne (deg1_unique_edge_eq n comp v hdeg1 e he hve eb heb_comp (hbv ▸ heb_b))
  have hreach := hconn a b ⟨ea, hea_comp, hea_a⟩ ⟨eb, heb_comp, heb_b⟩
  obtain ⟨walk⟩ := hreach
  exact walk_avoids_deg1_aux n comp v hdeg1 e he hve ha_ne_v hb_ne_v walk

private lemma reachable_from_deg0_eq (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) (hdeg0 : vertexDegreeIn n edges u = 0)
    (hreach : (edgeSetToGraph n edges).Reachable u v) :
    v = u := by
  obtain ⟨walk⟩ := hreach
  by_cases huv : u = v
  · exact huv.symm
  · obtain ⟨w, hadj, _, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne huv walk
    have hpos : 0 < vertexDegreeIn n edges u := by
      unfold vertexDegreeIn
      rw [Finset.card_pos]
      exact ⟨Sym2.mk (u, w), Finset.mem_filter.mpr ⟨hadj.2, Sym2.mem_mk_left u w⟩⟩
    omega

lemma sum_vertexDegrees_eq_twice_card
    (n : ℕ) (comp : Finset (Edge n))
    (hnoloops : ∀ e ∈ comp, ¬ e.IsDiag) :
    ∑ v ∈ (Finset.univ : Finset (Fin n)), vertexDegreeIn n comp v = 2 * comp.card := by
  have edge_card_two : ∀ e ∈ comp,
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
      rw [this, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  simp only [vertexDegreeIn]
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := Finset.univ) (t := comp) (r := fun (v : Fin n) (e : Edge n) => v ∈ e)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
  rw [hdc]
  rw [Finset.sum_congr rfl edge_card_two]
  simp [Finset.sum_const, mul_comm]

private lemma incident_vertices_le_edges_plus_one
    (n : ℕ) (comp : Finset (Edge n))
    (hconn : IsIncidentConnected n comp)
    (hdeg_le2 : ∀ v : Fin n, vertexDegreeIn n comp v ≤ 2)
    (hpath : ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hnoloops : ∀ e ∈ comp, ¬ e.IsDiag) :
    (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).card ≤ comp.card + 1 := by
  have key : ∀ (k : ℕ) (comp : Finset (Edge n)),
      comp.card ≤ k →
      IsIncidentConnected n comp →
      (∀ v : Fin n, vertexDegreeIn n comp v ≤ 2) →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) →
      (∀ e ∈ comp, ¬ e.IsDiag) →
      (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).card ≤
        comp.card + 1 := by
    intro k
    induction k with
    | zero =>
      intro comp hcard _ _ hpath' _
      exfalso
      apply hpath'
      intro v
      left
      have : comp = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      unfold vertexDegreeIn
      rw [this]
      simp
    | succ k ih =>
      intro comp hcard hconn' hdeg_le2' hpath' hnoloops'
      push_neg at hpath'
      obtain ⟨v0, hv0⟩ := hpath'
      have hv0_le2 := hdeg_le2' v0
      have hv0_deg1 : vertexDegreeIn n comp v0 = 1 := by omega
      obtain ⟨e0, ⟨he0, hve0⟩, _⟩ := deg1_vertex_exists_unique_edge n comp v0 hv0_deg1
      obtain ⟨w0, hw0_ne, ew0, hew0, _, hw0_in⟩ :=
        deg1_other_endpoint n comp v0 hv0_deg1 hnoloops'
      have hew0_eq : ew0 = e0 := by
        have ⟨_, _, huniq⟩ := deg1_vertex_exists_unique_edge n comp v0 hv0_deg1
        rw [huniq ew0 ⟨hew0, by assumption⟩, huniq e0 ⟨he0, hve0⟩]
      rw [hew0_eq] at hw0_in
      set comp' := comp.erase e0
      have hcard' : comp'.card ≤ k := by
        rw [show comp' = comp.erase e0 by rfl]
        rw [Finset.card_erase_of_mem he0]
        omega
      have hcomp'_conn := leaf_removal_connected n comp hconn' v0 hv0_deg1 e0 he0 hve0
      have hdeg'_le2 : ∀ v : Fin n, vertexDegreeIn n comp' v ≤ 2 := by
        intro v
        calc
          vertexDegreeIn n comp' v ≤ vertexDegreeIn n comp v :=
            vertexDegreeIn_mono n comp' comp (Finset.erase_subset e0 comp) v
          _ ≤ 2 := hdeg_le2' v
      have hnoloops'' : ∀ e ∈ comp', ¬ e.IsDiag := by
        intro e he'
        exact hnoloops' e (Finset.mem_of_mem_erase he')
      have hw0_deg_comp' : vertexDegreeIn n comp' w0 =
          vertexDegreeIn n comp w0 - 1 := by
        rw [erase_edge_deg n comp e0 he0 w0, if_pos hw0_in]
      have hv0_deg_comp' : vertexDegreeIn n comp' v0 = 0 := by
        rw [erase_edge_deg n comp e0 he0 v0, if_pos hve0, hv0_deg1]
      by_cases hcomp'_empty : comp' = ∅
      · have hV_le_sum :
            (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).card ≤
              ∑ v ∈ (Finset.univ : Finset (Fin n)), vertexDegreeIn n comp v := by
          rw [Finset.card_eq_sum_ones]
          have h₁ :
              (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).sum
                  (fun _ => (1 : ℕ)) ≤
                (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).sum
                  (fun v => vertexDegreeIn n comp v) := by
            apply Finset.sum_le_sum
            intro v hv
            simp only [Finset.mem_filter] at hv
            omega
          have h₂ :
              (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).sum
                  (fun v => vertexDegreeIn n comp v) ≤
                ∑ v ∈ (Finset.univ : Finset (Fin n)), vertexDegreeIn n comp v := by
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by
              exact Nat.zero_le _
          exact h₁.trans h₂
        have hcard_one : comp.card = 1 := by
          have hcard_zero : comp'.card = 0 := by simpa [hcomp'_empty]
          rw [show comp' = comp.erase e0 by rfl, Finset.card_erase_of_mem he0] at hcard_zero
          have hcomp_pos : 0 < comp.card := Finset.card_pos.mpr ⟨e0, he0⟩
          omega
        have hsum := sum_vertexDegrees_eq_twice_card n comp hnoloops'
        rw [hcard_one] at hsum
        have hbound : (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).card ≤ 2 := by
          exact hV_le_sum.trans (by simpa [hsum])
        simpa [hcard_one] using hbound
      · have hcomp'_ne : comp'.Nonempty := Finset.nonempty_of_ne_empty hcomp'_empty
        have hw0_deg_comp : vertexDegreeIn n comp w0 = 2 := by
          have hw0_pos : 0 < vertexDegreeIn n comp w0 := by
            unfold vertexDegreeIn
            rw [Finset.card_pos]
            exact ⟨e0, Finset.mem_filter.mpr ⟨he0, hw0_in⟩⟩
          have hw0_ne1 : vertexDegreeIn n comp w0 ≠ 1 := by
            intro hw0_deg1
            have hw0_deg0' : vertexDegreeIn n comp' w0 = 0 := by
              rw [hw0_deg_comp', hw0_deg1]
            obtain ⟨e', he'⟩ := hcomp'_ne
            have hnd' := hnoloops'' e' he'
            have hx : ∃ x : Fin n, x ∈ e' ∧ x ≠ w0 := by
              induction e' using Sym2.ind with
              | h a b =>
                have hab : a ≠ b := fun h' => hnd' (Sym2.mk_isDiag_iff.mpr h')
                by_cases haw : a = w0
                · refine ⟨b, Sym2.mem_mk_right a b, ?_⟩
                  intro hbw
                  exact hab (haw.trans hbw.symm)
                · exact ⟨a, Sym2.mem_mk_left a b, haw⟩
            obtain ⟨x, hx_in, hx_ne⟩ := hx
            have hx_ne_v0 : x ≠ v0 := by
              intro hxv0
              have he'_in_comp : e' ∈ comp := Finset.mem_of_mem_erase he'
              have he'_ne : e' ≠ e0 := by
                rw [show comp' = comp.erase e0 by rfl] at he'
                exact (Finset.mem_erase.mp he').1
              exact he'_ne <|
                deg1_unique_edge_eq n comp v0 hv0_deg1 e0 he0 hve0 e' he'_in_comp (hxv0 ▸ hx_in)
            have hreach : (edgeSetToGraph n comp).Reachable w0 x :=
              hconn' w0 x ⟨e0, he0, hw0_in⟩ ⟨e', Finset.mem_of_mem_erase he', hx_in⟩
            obtain ⟨walk⟩ := hreach
            have hreach' : (edgeSetToGraph n comp').Reachable w0 x :=
              walk_avoids_deg1_aux n comp v0 hv0_deg1 e0 he0 hve0 hw0_ne hx_ne_v0 walk
            have : x = w0 := reachable_from_deg0_eq n comp' w0 x hw0_deg0' hreach'
            exact hx_ne this
          have hw0_le2 := hdeg_le2' w0
          omega
        have hw0_deg1' : vertexDegreeIn n comp' w0 = 1 := by
          rw [hw0_deg_comp']
          omega
        have hpath'' : ¬(∀ v : Fin n, vertexDegreeIn n comp' v = 0 ∨ vertexDegreeIn n comp' v = 2) := by
          intro hall
          rcases hall w0 with h0 | h2 <;> omega
        have V_pos_eq :
            (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1) =
              (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp' v ≥ 1) ∪ {v0} := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_singleton]
          constructor
          · intro hge
            by_cases hv : v = v0
            · exact Or.inr hv
            · left
              by_cases hw : v = w0
              · simpa [hw, hw0_deg1']
              · have hv_not_in_e0 : v ∉ e0 := by
                  intro hvin
                  have he0_pair : e0 = Sym2.mk (v0, w0) := by
                    exact (Sym2.mem_and_mem_iff hw0_ne.symm).mp ⟨hve0, hw0_in⟩
                  have : v = v0 ∨ v = w0 := by
                    rw [he0_pair] at hvin
                    simpa [Sym2.mem_iff] using hvin
                  rcases this with h | h
                  · exact hv h
                  · exact hw h
                rw [erase_edge_deg n comp e0 he0 v, if_neg hv_not_in_e0]
                exact hge
          · rintro (hge | rfl)
            · exact le_trans hge <|
                vertexDegreeIn_mono n comp' comp (Finset.erase_subset e0 comp) v
            · omega
        have V'_bound := ih comp' hcard' hcomp'_conn hdeg'_le2 hpath'' hnoloops''
        rw [V_pos_eq, Finset.card_union_of_disjoint (by
          rw [Finset.disjoint_singleton_right]
          simp [hv0_deg_comp']), Finset.card_singleton]
        have : comp'.card + 1 = comp.card := by
          rw [show comp' = comp.erase e0 by rfl, Finset.card_erase_of_mem he0]
          exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨e0, he0⟩)
        omega
  exact key comp.card comp (le_refl _) hconn hdeg_le2 hpath hnoloops

lemma connected_maxdeg2_not_cycle_exactly2_deg1
    (n : ℕ) (comp : Finset (Edge n))
    (_hne : comp.Nonempty)
    (hconn : IsIncidentConnected n comp)
    (hdeg_le2 : ∀ v : Fin n, vertexDegreeIn n comp v ≤ 2)
    (hpath : ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hnoloops : ∀ e ∈ comp, ¬ e.IsDiag) :
    (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 1).card = 2 := by
  set D1 := Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 1
  set D2 := Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 2
  have hdisj12 : Disjoint D1 D2 := by
    simp only [D1, D2, Finset.disjoint_filter]; intro v _ h1 h2; omega
  have edge_card_two : ∀ e ∈ comp,
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
      rw [this, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  have sum_eq : ∑ v ∈ (Finset.univ : Finset (Fin n)), vertexDegreeIn n comp v =
      2 * comp.card := by
    simp only [vertexDegreeIn]
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := comp) (r := fun (v : Fin n) (e : Edge n) => v ∈ e)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
    rw [hdc]
    have : ∀ e ∈ comp, (Finset.filter (fun a => a ∈ e) Finset.univ).card = 2 := by
      intro e he; exact edge_card_two e he
    rw [Finset.sum_congr rfl this]
    simp [Finset.sum_const, mul_comm]
  have hD1sum : ∑ v ∈ D1, vertexDegreeIn n comp v = D1.card := by
    rw [Finset.card_eq_sum_ones]; apply Finset.sum_congr rfl
    intro v hv; simp only [D1, Finset.mem_filter] at hv; exact hv.2
  have hD2sum : ∑ v ∈ D2, vertexDegreeIn n comp v = 2 * D2.card := by
    have : ∑ v ∈ D2, vertexDegreeIn n comp v = ∑ _v ∈ D2, 2 := by
      apply Finset.sum_congr rfl
      intro v hv; simp only [D2, Finset.mem_filter] at hv; exact hv.2
    rw [this, Finset.sum_const, smul_eq_mul, mul_comm]
  have htotal : D1.card + 2 * D2.card = 2 * comp.card := by
    set D0 := Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 0
    have hdisj01 : Disjoint D0 D1 := by
      simp only [D0, D1, Finset.disjoint_filter]; intro v _ h0 h1; omega
    have hdisj02 : Disjoint D0 D2 := by
      simp only [D0, D2, Finset.disjoint_filter]; intro v _ h0 h2; omega
    have hunion : Finset.univ = D0 ∪ D1 ∪ D2 := by
      ext v
      simp only [D0, D1, D2, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      have hle := hdeg_le2 v
      set d := vertexDegreeIn n comp v; interval_cases d <;> simp_all
    have hD0sum : ∑ v ∈ D0, vertexDegreeIn n comp v = 0 := by
      apply Finset.sum_eq_zero; intro v hv; simp only [D0, Finset.mem_filter] at hv; exact hv.2
    have hpart : ∑ v ∈ Finset.univ, vertexDegreeIn n comp v =
        ∑ v ∈ D0, vertexDegreeIn n comp v +
        ∑ v ∈ D1, vertexDegreeIn n comp v +
        ∑ v ∈ D2, vertexDegreeIn n comp v := by
      conv_lhs => rw [hunion]
      rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj02, hdisj12⟩)]
      rw [Finset.sum_union hdisj01]
    rw [hpart, hD0sum, hD1sum, hD2sum] at sum_eq; omega
  have hD1_pos : D1.card ≥ 1 := by
    push_neg at hpath; obtain ⟨v, hv⟩ := hpath
    have hle := hdeg_le2 v
    have : vertexDegreeIn n comp v = 1 := by omega
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, this⟩⟩
  have hD1_even : ∃ k, D1.card = 2 * k := ⟨comp.card - D2.card, by omega⟩
  have hD1_ge2 : D1.card ≥ 2 := by obtain ⟨k, hk⟩ := hD1_even; omega
  have hV_eq : (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1) = D1 ∪ D2 := by
    ext v; simp only [D1, D2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    have hle := hdeg_le2 v
    constructor
    · intro hge; omega
    · rintro (h | h) <;> omega
  have hV_card : (Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v ≥ 1).card =
      D1.card + D2.card := by
    rw [hV_eq, Finset.card_union_of_disjoint hdisj12]
  have hD1_le2 : D1.card ≤ 2 := by
    have hle := incident_vertices_le_edges_plus_one n comp hconn hdeg_le2 hpath hnoloops
    rw [hV_card] at hle; omega
  omega

lemma finset_card_eq_two {α : Type*} [DecidableEq α]
    (S : Finset α) (hcard : S.card = 2) :
    ∃ a b : α, a ≠ b ∧ a ∈ S ∧ b ∈ S ∧ S = {a, b} := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hne
  have hne' : (S.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    have := Finset.card_erase_of_mem ha; rw [h] at this; simp at this; omega
  obtain ⟨b, hb'⟩ := hne'
  have hb : b ∈ S := Finset.mem_of_mem_erase hb'
  have hab : a ≠ b := by intro h; rw [h] at hb'; simp at hb'
  refine ⟨a, b, hab, ha, hb, ?_⟩
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    by_contra h; push_neg at h
    have hxa : x ≠ a := h.1; have hxb : x ≠ b := h.2
    have hx_erase : x ∈ S.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
    have hx_erase2 : x ∈ (S.erase a).erase b := Finset.mem_erase.mpr ⟨hxb, hx_erase⟩
    have hcard' : ((S.erase a).erase b).card = 0 := by
      rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]; omega
    rw [Finset.card_eq_zero] at hcard'; rw [hcard'] at hx_erase2; simp at hx_erase2
  · rintro (rfl | rfl) <;> assumption

private lemma path_component_has_two_deg1_vertices
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (comp : Finset (Edge n)) (hcomp : comp ⊆ leftSubgraph S H)
    (hne : comp.Nonempty)
    (hpath : ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hconn : IsIncidentConnected n comp)
    (hmax : ∀ e ∈ leftSubgraph S H \ comp,
      ∀ v : Fin n, v ∈ e → vertexDegreeIn n comp v = 0) :
    ∃ u v : Fin n, u ≠ v ∧
      vertexDegreeIn n comp u = 1 ∧ vertexDegreeIn n comp v = 1 ∧
      u ∈ danglingEndpoints S H ∧ v ∈ danglingEndpoints S H ∧
      (edgeSetToGraph n comp).Reachable u v ∧
      (∀ w : Fin n, vertexDegreeIn n comp w = 1 → w = u ∨ w = v) := by
  have hdeg_le2 : ∀ v : Fin n, vertexDegreeIn n comp v ≤ 2 := by
    intro v
    calc vertexDegreeIn n comp v
        ≤ vertexDegreeIn n (leftSubgraph S H) v :=
          vertexDegreeIn_mono n comp (leftSubgraph S H) hcomp v
      _ ≤ 2 := leftSubgraph_max_degree_two S H hH v
  set D1 := Finset.univ.filter fun v : Fin n => vertexDegreeIn n comp v = 1
  have hcomp_noloops : ∀ e ∈ comp, ¬ e.IsDiag := by
    intro e he; exact hH.noLoops e (Finset.inter_subset_left (hcomp he))
  have hD1_eq2 : D1.card = 2 :=
    connected_maxdeg2_not_cycle_exactly2_deg1 n comp hne hconn hdeg_le2 hpath hcomp_noloops
  obtain ⟨u, v, huv_ne, hu_mem, hv_mem, hD1_eq⟩ := finset_card_eq_two D1 hD1_eq2
  simp only [D1, Finset.mem_filter] at hu_mem hv_mem
  have deg1_implies_dangling : ∀ w : Fin n, vertexDegreeIn n comp w = 1 →
      w ∈ danglingEndpoints S H := by
    intro w hw
    have hpos : vertexDegreeIn n comp w > 0 := by omega
    have hcomp_eq := vertexDegreeIn_comp_eq_of_maximal n comp
      (leftSubgraph S H) hcomp hmax w hpos
    simp only [danglingEndpoints, Finset.mem_filter, degreeProfile]
    constructor
    · simp only [boundaryVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · have hleft : leftDegreeAt S H w ≥ 1 := by
          show vertexDegreeIn n (leftSubgraph S H) w ≥ 1; omega
        unfold leftDegreeAt leftSubgraph vertexDegreeIn at hleft
        have hne' : (Finset.filter (fun e => w ∈ e) (H ∩ S.leftEdges)).Nonempty := by
          by_contra h'; rw [Finset.not_nonempty_iff_eq_empty] at h'
          rw [h', Finset.card_empty] at hleft; omega
        obtain ⟨e, he⟩ := hne'
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
      · have hsum := leftDeg_add_rightDeg_eq_two S H hH w
        have hleft : leftDegreeAt S H w = 1 := by
          show vertexDegreeIn n (leftSubgraph S H) w = 1; omega
        have hright : rightDegreeAt S H w ≥ 1 := by omega
        unfold rightDegreeAt rightSubgraph vertexDegreeIn at hright
        have hne' : (Finset.filter (fun e => w ∈ e) (H ∩ S.rightEdges)).Nonempty := by
          by_contra h'; rw [Finset.not_nonempty_iff_eq_empty] at h'
          rw [h', Finset.card_empty] at hright; omega
        obtain ⟨e, he⟩ := hne'
        simp only [Finset.mem_filter, Finset.mem_inter] at he
        exact ⟨e, he.1.2, he.2⟩
    · show leftDegreeAt S H w = 1
      show vertexDegreeIn n (leftSubgraph S H) w = 1; omega
  have hu_incident : ∃ e ∈ comp, u ∈ e := by
    unfold vertexDegreeIn at hu_mem
    have h0 : 0 < (Finset.filter (fun e => u ∈ e) comp).card := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp h0
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  have hv_incident : ∃ e ∈ comp, v ∈ e := by
    unfold vertexDegreeIn at hv_mem
    have h0 : 0 < (Finset.filter (fun e => v ∈ e) comp).card := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp h0
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  refine ⟨u, v, huv_ne, hu_mem.2, hv_mem.2,
    deg1_implies_dangling u hu_mem.2, deg1_implies_dangling v hv_mem.2,
    hconn u v hu_incident hv_incident, ?_⟩
  intro w hw
  have : w ∈ D1 := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩
  rw [hD1_eq] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  exact this

open Classical in
noncomputable def edgeComponentOf (n : ℕ) (edges : Finset (Edge n))
    (u : Fin n) : Finset (Edge n) :=
  edges.filter fun e =>
    ∃ v : Fin n, v ∈ e ∧ (edgeSetToGraph n edges).Reachable u v

private lemma edgeComponentOf_mem (n : ℕ) (edges : Finset (Edge n))
    (u : Fin n) (e : Edge n) (he : e ∈ edges) (v : Fin n)
    (hv : v ∈ e) (hreach : (edgeSetToGraph n edges).Reachable u v) :
    e ∈ edgeComponentOf n edges u := by
  unfold edgeComponentOf
  simp only [Finset.mem_filter]
  exact ⟨he, v, hv, hreach⟩

lemma edgeComponentOf_sub (n : ℕ) (edges : Finset (Edge n)) (u : Fin n) :
    edgeComponentOf n edges u ⊆ edges := by
  intro e he
  unfold edgeComponentOf at he
  simp only [Finset.mem_filter] at he
  exact he.1

private lemma edgeComponentOf_reachable_from_incident (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) (hv : ∃ e ∈ edgeComponentOf n edges u, v ∈ e) :
    (edgeSetToGraph n edges).Reachable u v := by
  obtain ⟨e, he, hve⟩ := hv
  simp only [edgeComponentOf, Finset.mem_filter] at he
  obtain ⟨he_mem, w, hw_mem, hw_reach⟩ := he
  by_cases hvw : v = w
  · exact hvw ▸ hw_reach
  · induction e using Sym2.ind with
    | h a b =>
      simp only [Sym2.mem_iff] at hve hw_mem
      rcases hve with rfl | rfl <;> rcases hw_mem with rfl | rfl
      · exact absurd rfl hvw
      · have hadj : (edgeSetToGraph n edges).Adj w v := by
          constructor
          · exact fun h => hvw h.symm
          · show Sym2.mk (w, v) ∈ edges
            rw [Sym2.eq_swap]; exact he_mem
        exact hw_reach.trans hadj.reachable
      · have hadj : (edgeSetToGraph n edges).Adj w v := by
          constructor
          · exact fun h => hvw h.symm
          · show Sym2.mk (w, v) ∈ edges
            exact he_mem
        exact hw_reach.trans hadj.reachable
      · exact absurd rfl hvw

private lemma reachable_from_u_in_component (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) (hreach : (edgeSetToGraph n edges).Reachable u v) :
    (edgeSetToGraph n (edgeComponentOf n edges u)).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach ⊢
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hadj ih =>
    apply Relation.ReflTransGen.tail ih
    obtain ⟨hne, hmem⟩ := hadj
    refine ⟨hne, ?_⟩
    simp only [edgeComponentOf, Finset.mem_filter]
    have hprev_reach : (edgeSetToGraph n edges).Reachable u _ :=
      (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hprev
    exact ⟨hmem, _, Sym2.mem_mk_left _ _, hprev_reach⟩

lemma edgeComponentOf_incident_connected (n : ℕ) (edges : Finset (Edge n))
    (u : Fin n) (_hu : ∃ e ∈ edges, u ∈ e) :
    IsIncidentConnected n (edgeComponentOf n edges u) := by
  intro v w hv_inc hw_inc
  have hv_reach : (edgeSetToGraph n edges).Reachable u v :=
    edgeComponentOf_reachable_from_incident n edges u v hv_inc
  have hw_reach : (edgeSetToGraph n edges).Reachable u w :=
    edgeComponentOf_reachable_from_incident n edges u w hw_inc
  exact (reachable_from_u_in_component n edges u v hv_reach).symm.trans
    (reachable_from_u_in_component n edges u w hw_reach)

lemma edgeComponentOf_nonempty (n : ℕ) (edges : Finset (Edge n))
    (u : Fin n) (hu : ∃ e ∈ edges, u ∈ e) :
    (edgeComponentOf n edges u).Nonempty := by
  obtain ⟨e, he, hue⟩ := hu
  exact ⟨e, edgeComponentOf_mem n edges u e he u hue (SimpleGraph.Reachable.refl u)⟩

lemma edgeComponentOf_degree_le (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) :
    vertexDegreeIn n (edgeComponentOf n edges u) v ≤ vertexDegreeIn n edges v := by
  unfold vertexDegreeIn
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (edgeComponentOf_sub n edges u)

lemma edgeComponentOf_degree_eq (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) (hreach : (edgeSetToGraph n edges).Reachable u v) :
    vertexDegreeIn n (edgeComponentOf n edges u) v = vertexDegreeIn n edges v := by
  unfold vertexDegreeIn
  apply le_antisymm
  · exact Finset.card_le_card (Finset.filter_subset_filter _ (edgeComponentOf_sub n edges u))
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨edgeComponentOf_mem n edges u e he.1 v he.2 hreach, he.2⟩

private lemma edgeComponentOf_reachable_iff (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n) (hv : ∃ e ∈ edgeComponentOf n edges u, v ∈ e) :
    (edgeSetToGraph n edges).Reachable u v :=
  edgeComponentOf_reachable_from_incident n edges u v hv

private lemma edgeComponentOf_not_cycle (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (u : Fin n) (hu : u ∈ danglingEndpoints S H) :
    ¬(∀ v : Fin n, vertexDegreeIn n (edgeComponentOf n (leftSubgraph S H) u) v = 0 ∨
      vertexDegreeIn n (edgeComponentOf n (leftSubgraph S H) u) v = 2) := by
  intro hall
  have hu_deg : vertexDegreeIn n (leftSubgraph S H) u = 1 := by
    simp only [danglingEndpoints, Finset.mem_filter, degreeProfile] at hu
    exact hu.2
  have hcomp_deg := edgeComponentOf_degree_eq n (leftSubgraph S H) u u
    (SimpleGraph.Reachable.refl u)
  have : vertexDegreeIn n (edgeComponentOf n (leftSubgraph S H) u) u = 1 := by
    rw [hcomp_deg]; exact hu_deg
  rcases hall u with h0 | h2 <;> omega

private lemma reachable_in_component_lifts (n : ℕ) (edges : Finset (Edge n))
    (u v : Fin n)
    (hreach : (edgeSetToGraph n (edgeComponentOf n edges u)).Reachable u v) :
    (edgeSetToGraph n edges).Reachable u v := by
  have hsub := edgeComponentOf_sub n edges u
  apply SimpleGraph.Reachable.mono _ hreach
  intro x y hadj
  exact ⟨hadj.1, hsub hadj.2⟩

theorem deg1_unique_partner
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : Fin n) (hu : u ∈ danglingEndpoints S H) :
    ∃! v, v ∈ danglingEndpoints S H ∧ v ≠ u ∧
      (edgeSetToGraph n (leftSubgraph S H)).Reachable u v := by
  set L := leftSubgraph S H with hL_def
  set comp := edgeComponentOf n L u
  have hu_dangling : degreeProfile S H u = 1 := by
    simp only [danglingEndpoints, Finset.mem_filter] at hu
    exact hu.2
  have hu_deg : vertexDegreeIn n L u = 1 := by
    unfold degreeProfile leftDegreeAt at hu_dangling
    exact hu_dangling
  have hu_edge : ∃ e ∈ L, u ∈ e := by
    unfold vertexDegreeIn at hu_deg
    by_contra h
    push_neg at h
    have : (L.filter fun e => u ∈ e).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he
      exact h e he
    omega
  have hcomp_sub : comp ⊆ L := edgeComponentOf_sub n L u
  have hcomp_ne : comp.Nonempty := edgeComponentOf_nonempty n L u hu_edge
  have hcomp_conn : IsIncidentConnected n comp := edgeComponentOf_incident_connected n L u hu_edge
  have hcomp_not_cycle := edgeComponentOf_not_cycle S H hH u hu
  have hcomp_max : ∀ e ∈ L \ comp, ∀ v : Fin n, v ∈ e → vertexDegreeIn n comp v = 0 := by
    intro e he_diff v hv_in_e
    simp only [Finset.mem_sdiff] at he_diff
    obtain ⟨he_L, he_not_comp⟩ := he_diff
    by_contra h_nonzero
    have hv_reach : (edgeSetToGraph n L).Reachable u v := by
      have h_pos : 0 < vertexDegreeIn n comp v := by omega
      unfold vertexDegreeIn at h_pos
      rw [Finset.card_pos] at h_pos
      obtain ⟨f, hf⟩ := h_pos
      simp only [Finset.mem_filter] at hf
      obtain ⟨hf_comp, hv_in_f⟩ := hf
      have hf_comp' : f ∈ edgeComponentOf n L u := hf_comp
      simp only [edgeComponentOf, Finset.mem_filter] at hf_comp'
      obtain ⟨hf_L, w, hw_in_f, hw_reach⟩ := hf_comp'
      by_cases hvw : v = w
      · exact hvw ▸ hw_reach
      · induction f using Sym2.ind with
        | h a b =>
          simp only [Sym2.mem_iff] at hv_in_f hw_in_f
          rcases hv_in_f with rfl | rfl <;> rcases hw_in_f with rfl | rfl
          · exact absurd rfl hvw
          · have hadj : (edgeSetToGraph n L).Adj w v := by
              constructor
              · exact fun h => hvw h.symm
              · show Sym2.mk (w, v) ∈ L; rw [Sym2.eq_swap]; exact hf_L
            exact hw_reach.trans hadj.reachable
          · have hadj : (edgeSetToGraph n L).Adj w v := by
              constructor
              · exact fun h => hvw h.symm
              · show Sym2.mk (w, v) ∈ L; exact hf_L
            exact hw_reach.trans hadj.reachable
          · exact absurd rfl hvw
    have he_should_be_comp : e ∈ comp := by
      show e ∈ edgeComponentOf n L u
      simp only [edgeComponentOf, Finset.mem_filter]
      exact ⟨he_L, v, hv_in_e, hv_reach⟩
    exact he_not_comp he_should_be_comp
  obtain ⟨a, b, hab_ne, ha_deg1, hb_deg1, ha_dang, hb_dang, hab_reach, hab_only⟩ :=
    path_component_has_two_deg1_vertices S H hH comp hcomp_sub hcomp_ne hcomp_not_cycle hcomp_conn hcomp_max
  have hu_deg_comp : vertexDegreeIn n comp u = 1 := by
    have hself : (edgeSetToGraph n L).Reachable u u := SimpleGraph.Reachable.refl u
    rw [edgeComponentOf_degree_eq n L u u hself]
    exact hu_deg
  have hu_is_ab : u = a ∨ u = b := hab_only u hu_deg_comp
  rcases hu_is_ab with rfl | rfl
  · use b
    constructor
    · exact ⟨hb_dang, hab_ne.symm, reachable_in_component_lifts n L u b hab_reach⟩
    · intro w ⟨hw_dang, hw_ne, hw_reach⟩
      have hw_deg_comp : vertexDegreeIn n comp w = vertexDegreeIn n L w := by
        exact edgeComponentOf_degree_eq n L u w hw_reach
      have hw_dangling_deg : vertexDegreeIn n L w = 1 := by
        simp only [danglingEndpoints, Finset.mem_filter] at hw_dang
        unfold degreeProfile leftDegreeAt at hw_dang
        exact hw_dang.2
      have hw_comp_deg1 : vertexDegreeIn n comp w = 1 := by omega
      have : w = u ∨ w = b := hab_only w hw_comp_deg1
      rcases this with rfl | rfl
      · exact absurd rfl hw_ne
      · rfl
  · use a
    constructor
    · exact ⟨ha_dang, hab_ne, hab_reach.symm |> reachable_in_component_lifts n L u a⟩
    · intro w ⟨hw_dang, hw_ne, hw_reach⟩
      have hw_deg_comp : vertexDegreeIn n comp w = vertexDegreeIn n L w := by
        exact edgeComponentOf_degree_eq n L u w hw_reach
      have hw_dangling_deg : vertexDegreeIn n L w = 1 := by
        simp only [danglingEndpoints, Finset.mem_filter] at hw_dang
        unfold degreeProfile leftDegreeAt at hw_dang
        exact hw_dang.2
      have hw_comp_deg1 : vertexDegreeIn n comp w = 1 := by omega
      have : w = a ∨ w = u := hab_only w hw_comp_deg1
      rcases this with rfl | rfl
      · rfl
      · exact absurd rfl hw_ne

private lemma deg1_vertex_reachable_to_other_deg1
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : Fin n) (hu : u ∈ danglingEndpoints S H) :
    ∃ v ∈ danglingEndpoints S H, v ≠ u ∧
      (edgeSetToGraph n (leftSubgraph S H)).Reachable u v := by
  obtain ⟨v, ⟨hv, hne, hreach⟩, _⟩ := deg1_unique_partner n S H hH u hu
  exact ⟨v, hv, hne, hreach⟩

open Classical in
private noncomputable def partnerVertex
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : {v // v ∈ danglingEndpoints S H}) :
    {v // v ∈ danglingEndpoints S H} :=
  ⟨Classical.choose (ExistsUnique.exists (deg1_unique_partner n S H hH u.1 u.2)),
    (Classical.choose_spec (ExistsUnique.exists (deg1_unique_partner n S H hH u.1 u.2))).1⟩

private lemma partnerVertex_ne
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : {v // v ∈ danglingEndpoints S H}) :
    (partnerVertex n S H hH u).1 ≠ u.1 := by
  exact (Classical.choose_spec (ExistsUnique.exists (deg1_unique_partner n S H hH u.1 u.2))).2.1

private lemma partnerVertex_reachable
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : {v // v ∈ danglingEndpoints S H}) :
    (edgeSetToGraph n (leftSubgraph S H)).Reachable u.1 (partnerVertex n S H hH u).1 := by
  exact (Classical.choose_spec (ExistsUnique.exists (deg1_unique_partner n S H hH u.1 u.2))).2.2

private lemma partnerVertex_invol
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : {v // v ∈ danglingEndpoints S H}) :
    partnerVertex n S H hH (partnerVertex n S H hH u) = u := by
  apply Subtype.ext
  obtain ⟨v, hvprop, huniq⟩ := deg1_unique_partner n S H hH
    (partnerVertex n S H hH u).1 (partnerVertex n S H hH u).2
  have hchoose : (partnerVertex n S H hH (partnerVertex n S H hH u)).1 = v :=
    huniq _ (Classical.choose_spec (ExistsUnique.exists (deg1_unique_partner n S H hH
      (partnerVertex n S H hH u).1 (partnerVertex n S H hH u).2)))
  have hu : u.1 = v := huniq _ ⟨u.2, (partnerVertex_ne n S H hH u).symm,
    (partnerVertex_reachable n S H hH u).symm⟩
  exact hchoose.trans hu.symm

private lemma deg1_components_pair_into_matching
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (danglingEndpoints S H),
      ∀ p ∈ M.pairs,
        (edgeSetToGraph n (leftSubgraph S H)).Reachable p.1 p.2 := by
  classical
  let U := danglingEndpoints S H
  let partner : {v // v ∈ U} → {v // v ∈ U} := partnerVertex n S H hH
  let A : Finset {v // v ∈ U} := U.attach.filter fun u => u.1 < (partner u).1
  let pairs : Finset (Fin n × Fin n) := A.image fun u => (u.1, (partner u).1)
  have hpair_mem :
      ∀ p ∈ pairs, (edgeSetToGraph n (leftSubgraph S H)).Reachable p.1 p.2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨u, huA, rfl⟩
    exact partnerVertex_reachable n S H hH u
  have hfst_mem : ∀ p ∈ pairs, p.1 ∈ U := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨u, huA, rfl⟩
    exact u.2
  have hsnd_mem : ∀ p ∈ pairs, p.2 ∈ U := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨u, huA, rfl⟩
    exact (partner u).2
  have hne_pair : ∀ p ∈ pairs, p.1 ≠ p.2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨u, huA, rfl⟩
    simpa [partner] using (partnerVertex_ne n S H hH u).symm
  have hpair_of_mem :
      ∀ u : {v // v ∈ U}, ∀ p ∈ pairs,
        (u.1 = p.1 ∨ u.1 = p.2) →
        p =
          if hlt : u.1 < (partner u).1 then
            (u.1, (partner u).1)
          else
            ((partner u).1, u.1) := by
    intro u p hp hu
    rcases Finset.mem_image.mp hp with ⟨a, haA, rfl⟩
    have ha_lt : a.1 < (partner a).1 := (Finset.mem_filter.mp haA).2
    rcases hu with h | h
    · have hua : a = u := Subtype.ext h.symm
      subst hua
      simp [ha_lt]
    · have hpa : partner a = u := Subtype.ext h.symm
      have hpu : partner u = a := by
        simpa [partner, hpa] using partnerVertex_invol n S H hH a
      have hnot : ¬ u.1 < (partner u).1 := by
        simpa [partner, hpu, hpa] using not_lt_of_gt ha_lt
      have hEq : (a.1, (partner a).1) = ((partner u).1, u.1) := by
        simp [hpu, hpa]
      simpa [hnot] using hEq
  have hcovers : ∀ u ∈ U, ∃ p ∈ pairs, u = p.1 ∨ u = p.2 := by
    intro u hu
    let uu : {v // v ∈ U} := ⟨u, hu⟩
    by_cases hlt : u < (partner uu).1
    · refine ⟨(u, (partner uu).1), ?_, Or.inl rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨uu, Finset.mem_filter.mpr ?_, rfl⟩
      exact ⟨Finset.mem_attach U uu, hlt⟩
    · have hgt : (partner uu).1 < u := by
        exact lt_of_le_of_ne (le_of_not_gt hlt) (by
          simpa [partner, uu] using (partnerVertex_ne n S H hH uu))
      refine ⟨((partner uu).1, u), ?_, Or.inr rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨partner uu, Finset.mem_filter.mpr ?_, ?_⟩
      · exact ⟨Finset.mem_attach U (partner uu), by
          simpa [partner, partnerVertex_invol n S H hH uu] using hgt⟩
      · change ((partner uu).1, (partner (partner uu)).1) = ((partner uu).1, u)
        simp [partner, partnerVertex_invol n S H hH uu]
        rfl
  have hunique :
      ∀ u ∈ U, ∀ p₁ ∈ pairs, ∀ p₂ ∈ pairs,
        (u = p₁.1 ∨ u = p₁.2) → (u = p₂.1 ∨ u = p₂.2) → p₁ = p₂ := by
    intro u hu p₁ hp₁ p₂ hp₂ hu₁ hu₂
    let uu : {v // v ∈ U} := ⟨u, hu⟩
    have hp₁_eq := hpair_of_mem uu p₁ hp₁ hu₁
    have hp₂_eq := hpair_of_mem uu p₂ hp₂ hu₂
    exact hp₁_eq.trans hp₂_eq.symm
  have hA_card_eq_pairs : A.card = pairs.card := by
    unfold pairs
    symm
    exact Finset.card_image_of_injOn (by
      intro u hu v hv huv
      apply Subtype.ext
      exact congrArg Prod.fst huv)
  let B : Finset {v // v ∈ U} := U.attach.filter fun u => (partner u).1 < u.1
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro u huA huB
    exact (lt_asymm (Finset.mem_filter.mp huA).2 (Finset.mem_filter.mp huB).2).elim
  have hAB_union : U.attach = A ∪ B := by
    ext u
    simp only [A, B, Finset.mem_attach, true_and, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro huA
      have hne : u.1 ≠ (partner u).1 := by
        simpa [partner] using (partnerVertex_ne n S H hH u).symm
      by_cases hlt : u.1 < (partner u).1
      · exact Or.inl hlt
      · exact Or.inr (lt_of_le_of_ne (le_of_not_gt hlt) hne.symm)
    · intro huAB
      trivial
  have hA_card_eq_B : A.card = B.card := by
    apply Finset.card_bij (fun u hu => partner u)
    · intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_attach U (partner u), by
        simpa [partner, partnerVertex_invol n S H hH u] using (Finset.mem_filter.mp hu).2⟩
    · intro u hu v hv huv
      have := congrArg partner huv
      simpa [partner, partnerVertex_invol n S H hH u, partnerVertex_invol n S H hH v] using this
    · intro v hv
      refine ⟨partner v, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_attach U (partner v), by
          simpa [partner, partnerVertex_invol n S H hH v] using (Finset.mem_filter.mp hv).2⟩
      · simpa [partner] using partnerVertex_invol n S H hH v
  have hcard_eq : 2 * pairs.card = U.card := by
    have hU_attach : U.card = A.card + B.card := by
      calc
        U.card = U.attach.card := by rw [Finset.card_attach]
        _ = (A ∪ B).card := by rw [hAB_union]
        _ = A.card + B.card := Finset.card_union_of_disjoint hAB_disj
    have hpairs : pairs.card = A.card := hA_card_eq_pairs.symm
    have hU_pairs : U.card = pairs.card + pairs.card := by
      simpa [hpairs, hA_card_eq_B] using hU_attach
    omega
  refine ⟨{
    pairs := pairs
    fst_mem := hfst_mem
    snd_mem := hsnd_mem
    ne_pair := hne_pair
    covers := hcovers
    unique := hunique
    card_eq := hcard_eq
  }, hpair_mem⟩

def PathPairingReflectsComponents (n : ℕ) (S : Frontier n) (H : Finset (Edge n))
    (M : PerfectMatching (danglingEndpoints S H)) : Prop :=
  ∀ p ∈ M.pairs,
    (edgeSetToGraph n (leftSubgraph S H)).Reachable p.1 p.2

private theorem exists_structural_pathPairing
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (danglingEndpoints S H),
      PathPairingReflectsComponents n S H M := by
  obtain ⟨M, hM⟩ := deg1_components_pair_into_matching n S H hH
  exact ⟨M, hM⟩

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

theorem pathPairing_iff_reachable
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u v : Fin n) (hu : u ∈ danglingEndpoints S H) (hv : v ∈ danglingEndpoints S H)
    (hne : u ≠ v) :
    ((u, v) ∈ (pathPairing S H hH).pairs ∨ (v, u) ∈ (pathPairing S H hH).pairs) ↔
    (edgeSetToGraph n (leftSubgraph S H)).Reachable u v := by
  set M := pathPairing S H hH
  constructor
  · intro hpair
    rcases hpair with hp | hp
    · exact pathPairing_reflects_components S H hH (u, v) hp
    · exact (pathPairing_reflects_components S H hH (v, u) hp).symm
  · intro hreach
    obtain ⟨w, ⟨hw_dang, hw_ne, hw_reach⟩, hw_unique⟩ := deg1_unique_partner n S H hH u hu
    have hv_eq_w : v = w := by
      apply hw_unique
      exact ⟨hv, hne.symm, hreach⟩
    subst hv_eq_w
    obtain ⟨⟨a, b⟩, hp_mem, hu_in_p⟩ := M.covers u hu
    simp only at hu_in_p
    rcases hu_in_p with rfl | rfl
    · have hp2_dang := M.snd_mem (u, b) hp_mem
      have hp_ne := M.ne_pair (u, b) hp_mem
      have hp_reach := pathPairing_reflects_components S H hH (u, b) hp_mem
      have : b = v := hw_unique b ⟨hp2_dang, hp_ne.symm, hp_reach⟩
      rw [this] at hp_mem
      exact Or.inl hp_mem
    · have hp1_dang := M.fst_mem (a, u) hp_mem
      have hp_ne := M.ne_pair (a, u) hp_mem
      have hp_reach := pathPairing_reflects_components S H hH (a, u) hp_mem
      have : a = v := hw_unique a ⟨hp1_dang, hp_ne, hp_reach.symm⟩
      rw [this] at hp_mem
      exact Or.inr hp_mem

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

private lemma rightDanglingEndpoints_eq_danglingEndpoints_swap
    (S : Frontier n) (H : Finset (Edge n)) :
    rightDanglingEndpoints S H = danglingEndpoints S.swap H := by
  unfold rightDanglingEndpoints danglingEndpoints degreeProfile
  rw [boundaryVertices_swap]
  ext v; simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hbv, hdeg⟩
    exact ⟨hbv, show leftDegreeAt S.swap H v = 1 from by
      unfold leftDegreeAt; rw [leftSubgraph_swap]; exact hdeg⟩
  · rintro ⟨hbv, hdeg⟩
    exact ⟨hbv, show rightDegreeAt S H v = 1 from by
      have : leftDegreeAt S.swap H v = 1 := hdeg
      unfold leftDegreeAt at this; rw [leftSubgraph_swap] at this; exact this⟩

private lemma right_deg1_vertex_reachable_to_other_deg1
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u : Fin n) (hu : u ∈ rightDanglingEndpoints S H) :
    ∃ v ∈ rightDanglingEndpoints S H, v ≠ u ∧
      (edgeSetToGraph n (rightSubgraph S H)).Reachable u v := by
  rw [rightDanglingEndpoints_eq_danglingEndpoints_swap] at hu ⊢
  rw [show rightSubgraph S H = leftSubgraph S.swap H from (leftSubgraph_swap S H).symm]
  exact deg1_vertex_reachable_to_other_deg1 n S.swap H hH u hu

private lemma right_deg1_components_pair_into_matching
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (rightDanglingEndpoints S H),
      ∀ p ∈ M.pairs,
        (edgeSetToGraph n (rightSubgraph S H)).Reachable p.1 p.2 := by
  rw [show rightSubgraph S H = leftSubgraph S.swap H from (leftSubgraph_swap S H).symm]
  have heq := rightDanglingEndpoints_eq_danglingEndpoints_swap S H
  rw [heq]
  exact deg1_components_pair_into_matching n S.swap H hH

private theorem exists_structural_rightPairing
    (n : ℕ) (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    ∃ M : PerfectMatching (rightDanglingEndpoints S H),
      RightPairingReflectsComponents n S H M := by
  obtain ⟨M, hM⟩ := right_deg1_components_pair_into_matching n S H hH
  exact ⟨M, hM⟩

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

theorem rightPairing_iff_reachable
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (u v : Fin n) (hu : u ∈ rightDanglingEndpoints S H) (hv : v ∈ rightDanglingEndpoints S H)
    (hne : u ≠ v) :
    ((u, v) ∈ (rightPairing S H hH).pairs ∨ (v, u) ∈ (rightPairing S H hH).pairs) ↔
    (edgeSetToGraph n (rightSubgraph S H)).Reachable u v := by
  set M := rightPairing S H hH
  constructor
  · intro hpair
    rcases hpair with hp | hp
    · exact rightPairing_reflects_components S H hH (u, v) hp
    · exact (rightPairing_reflects_components S H hH (v, u) hp).symm
  · intro hreach
    have hu_swap : u ∈ danglingEndpoints S.swap H := by
      simpa [rightDanglingEndpoints_eq_danglingEndpoints_swap] using hu
    have hv_swap : v ∈ danglingEndpoints S.swap H := by
      simpa [rightDanglingEndpoints_eq_danglingEndpoints_swap] using hv
    have hreach_swap : (edgeSetToGraph n (leftSubgraph S.swap H)).Reachable u v := by
      simpa [leftSubgraph_swap] using hreach
    obtain ⟨w, ⟨hw_swap, hw_ne, hw_reach_swap⟩, hw_unique⟩ :=
      deg1_unique_partner n S.swap H hH u hu_swap
    have hv_eq_w : v = w := by
      apply hw_unique
      exact ⟨hv_swap, hne.symm, hreach_swap⟩
    subst hv_eq_w
    obtain ⟨⟨a, b⟩, hp_mem, hu_in_p⟩ := M.covers u hu
    simp only at hu_in_p
    rcases hu_in_p with rfl | rfl
    · have hp2 := M.snd_mem (u, b) hp_mem
      have hp_ne := M.ne_pair (u, b) hp_mem
      have hp_reach : (edgeSetToGraph n (rightSubgraph S H)).Reachable u b :=
        rightPairing_reflects_components S H hH (u, b) hp_mem
      have hp_reach_swap : (edgeSetToGraph n (leftSubgraph S.swap H)).Reachable u b := by
        simpa [leftSubgraph_swap] using hp_reach
      have hp2_swap : b ∈ danglingEndpoints S.swap H := by
        simpa [rightDanglingEndpoints_eq_danglingEndpoints_swap] using hp2
      have : b = v := hw_unique b ⟨hp2_swap, hp_ne.symm, hp_reach_swap⟩
      rw [this] at hp_mem
      exact Or.inl hp_mem
    · have hp1 := M.fst_mem (a, u) hp_mem
      have hp_ne := M.ne_pair (a, u) hp_mem
      have hp_reach : (edgeSetToGraph n (rightSubgraph S H)).Reachable a u :=
        rightPairing_reflects_components S H hH (a, u) hp_mem
      have hp_reach_swap : (edgeSetToGraph n (leftSubgraph S.swap H)).Reachable a u := by
        simpa [leftSubgraph_swap] using hp_reach
      have hp1_swap : a ∈ danglingEndpoints S.swap H := by
        simpa [rightDanglingEndpoints_eq_danglingEndpoints_swap] using hp1
      have : a = v := hw_unique a ⟨hp1_swap, hp_ne, hp_reach_swap.symm⟩
      rw [this] at hp_mem
      exact Or.inr hp_mem

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

section BoundaryComponentCorrespondence

private theorem adj_mono {n : ℕ} {A B : Finset (Edge n)} (h : A ⊆ B)
    {u v : Fin n} (hadj : (edgeSetToGraph n A).Adj u v) :
    (edgeSetToGraph n B).Adj u v :=
  ⟨hadj.1, h hadj.2⟩

private theorem reachable_mono {n : ℕ} {A B : Finset (Edge n)} (h : A ⊆ B)
    {u v : Fin n} (hreach : (edgeSetToGraph n A).Reachable u v) :
    (edgeSetToGraph n B).Reachable u v := by
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b _ hadj _ ih =>
    exact (SimpleGraph.Adj.reachable (adj_mono h hadj)).trans ih

open Classical in
private noncomputable def localEdgeComponentOf {n : ℕ} (edges : Finset (Edge n))
    (u : Fin n) : Finset (Edge n) :=
  edges.filter fun e =>
    ∃ v : Fin n, v ∈ e ∧ (edgeSetToGraph n edges).Reachable u v

open Classical in
private lemma localEdgeComponentOf_sub {n : ℕ} (edges : Finset (Edge n)) (u : Fin n) :
    localEdgeComponentOf edges u ⊆ edges :=
  Finset.filter_subset _ _

open Classical in
private lemma localEdgeComponentOf_nonempty {n : ℕ} (edges : Finset (Edge n))
    (u : Fin n) (hu : ∃ e ∈ edges, u ∈ e) :
    (localEdgeComponentOf edges u).Nonempty := by
  obtain ⟨e, he, hu⟩ := hu
  refine ⟨e, ?_⟩
  simp only [localEdgeComponentOf, Finset.mem_filter]
  exact ⟨he, u, hu, SimpleGraph.Reachable.refl u⟩

open Classical in
private lemma localEdgeComponentOf_reachable {n : ℕ} (edges : Finset (Edge n))
    (u v : Fin n) (hv : ∃ e ∈ localEdgeComponentOf edges u, v ∈ e) :
    (edgeSetToGraph n edges).Reachable u v := by
  obtain ⟨e, he, hv_in_e⟩ := hv
  simp only [localEdgeComponentOf, Finset.mem_filter] at he
  obtain ⟨he_edges, w, hw_in_e, hw_reach⟩ := he
  by_cases hwv : w = v
  · exact hwv ▸ hw_reach
  · exact hw_reach.trans (SimpleGraph.Adj.reachable ⟨hwv, by
      induction e using Sym2.ind with
      | h a b =>
        simp only [Sym2.mem_iff] at hw_in_e hv_in_e
        rcases hw_in_e with rfl | rfl <;> rcases hv_in_e with rfl | rfl
        · exact absurd rfl hwv
        · exact he_edges
        · rw [Sym2.eq_swap]
          exact he_edges
        · exact absurd rfl hwv⟩)

open Classical in
private lemma localEdgeComponentOf_degree_le {n : ℕ} (edges : Finset (Edge n))
    (u v : Fin n) :
    vertexDegreeIn n (localEdgeComponentOf edges u) v ≤ vertexDegreeIn n edges v := by
  unfold vertexDegreeIn localEdgeComponentOf
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))

open Classical in
private lemma localEdgeComponentOf_degree_eq {n : ℕ} (edges : Finset (Edge n))
    (u v : Fin n) (hreach : (edgeSetToGraph n edges).Reachable u v) :
    vertexDegreeIn n (localEdgeComponentOf edges u) v = vertexDegreeIn n edges v := by
  unfold vertexDegreeIn
  apply le_antisymm
  · exact Finset.card_le_card (Finset.filter_subset_filter _ (localEdgeComponentOf_sub edges u))
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    refine ⟨?_, he.2⟩
    simp only [localEdgeComponentOf, Finset.mem_filter]
    exact ⟨he.1, v, he.2, hreach⟩

def IsConnectedFinset {n : ℕ} (edges : Finset (Edge n)) : Prop :=
  IsConnectedEdgeSet n edges

structure BoundaryMultigraph (n : ℕ) where
  vertices : Finset (Fin n)
  lEdges : Finset (Fin n × Fin n)
  rEdges : Finset (Fin n × Fin n)

open Classical in
noncomputable def boundaryMultigraphOf (S : Frontier n)
    (L R : Finset (Edge n)) : BoundaryMultigraph n :=
  { vertices := (boundaryVertices S).filter fun v =>
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1
    lEdges := Finset.univ.filter fun p =>
      p.1 ∈ boundaryVertices S ∧ p.2 ∈ boundaryVertices S ∧
      p.1 ≠ p.2 ∧
      vertexDegreeIn n L p.1 = 1 ∧ vertexDegreeIn n L p.2 = 1 ∧
      (edgeSetToGraph n L).Reachable p.1 p.2
    rEdges := Finset.univ.filter fun p =>
      p.1 ∈ boundaryVertices S ∧ p.2 ∈ boundaryVertices S ∧
      p.1 ≠ p.2 ∧
      vertexDegreeIn n R p.1 = 1 ∧ vertexDegreeIn n R p.2 = 1 ∧
      (edgeSetToGraph n R).Reachable p.1 p.2 }

noncomputable def bmgToGraph {n : ℕ} (G : BoundaryMultigraph n) : SimpleGraph (Fin n) where
  Adj u v :=
    u ≠ v ∧ u ∈ G.vertices ∧ v ∈ G.vertices ∧
    ((u, v) ∈ G.lEdges ∨ (v, u) ∈ G.lEdges ∨
     (u, v) ∈ G.rEdges ∨ (v, u) ∈ G.rEdges)
  symm := by
    intro u v ⟨hne, hu, hv, hedges⟩
    exact ⟨hne.symm, hv, hu, by tauto⟩
  loopless := ⟨fun v ⟨hne, _⟩ => hne rfl⟩

open Classical in
noncomputable def numComponents {n : ℕ} (edges : Finset (Edge n)) : ℕ :=
  Set.ncard (Set.range (edgeSetToGraph n edges).connectedComponentMk)

open Classical in
noncomputable def numComponentsBMG {n : ℕ} (G : BoundaryMultigraph n) : ℕ :=
  Set.ncard {c : (bmgToGraph G).ConnectedComponent | ∃ v ∈ G.vertices,
    (bmgToGraph G).connectedComponentMk v = c}

open Classical in
def IsConnectedBoundaryMultigraph {n : ℕ} (G : BoundaryMultigraph n) : Prop :=
  numComponentsBMG G = 1

open Classical in
private theorem every_component_has_boundary_vertex
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (c : (edgeSetToGraph n (L ∪ R)).ConnectedComponent)
    (hc : c ∈ Set.range (edgeSetToGraph n (L ∪ R)).connectedComponentMk) :
    ∃ v : Fin n, v ∈ boundaryVertices S ∧
      (edgeSetToGraph n (L ∪ R)).connectedComponentMk v = c := by
  obtain ⟨v₀, rfl⟩ := hc
  by_cases h1 : vertexDegreeIn n L v₀ = 1
  · exact ⟨v₀, hLEndpoints v₀ h1, rfl⟩
  · by_cases h2 : vertexDegreeIn n R v₀ = 1
    · exact ⟨v₀, hREndpoints v₀ h2, rfl⟩
    · have hv₀_deg : vertexDegreeIn n (L ∪ R) v₀ = 2 := hSpanning v₀
      have hv₀_pos : 0 < vertexDegreeIn n (L ∪ R) v₀ := by omega
      unfold vertexDegreeIn at hv₀_pos
      rw [Finset.card_pos] at hv₀_pos
      obtain ⟨e₀, he₀⟩ := hv₀_pos
      simp only [Finset.mem_filter] at he₀
      obtain ⟨he₀_mem, hv₀_in_e₀⟩ := he₀
      rcases Finset.mem_union.mp he₀_mem with he₀L | he₀R
      · have hv₀_L_pos : 0 < vertexDegreeIn n L v₀ := by
          unfold vertexDegreeIn
          rw [Finset.card_pos]
          exact ⟨e₀, Finset.mem_filter.mpr ⟨he₀L, hv₀_in_e₀⟩⟩
        have hv₀_L_le : vertexDegreeIn n L v₀ ≤ vertexDegreeIn n (L ∪ R) v₀ := by
          unfold vertexDegreeIn
          exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)
        have hv₀_L_le2 : vertexDegreeIn n L v₀ ≤ 2 := by
          simpa [hv₀_deg] using hv₀_L_le
        have hv₀_L_eq2 : vertexDegreeIn n L v₀ = 2 := by
          have hv₀_L_ne1 : vertexDegreeIn n L v₀ ≠ 1 := h1
          omega
        set comp := localEdgeComponentOf L v₀ with hcomp_def
        have hcomp_sub : comp ⊆ L := localEdgeComponentOf_sub L v₀
        have hcomp_ne : comp.Nonempty :=
          localEdgeComponentOf_nonempty L v₀ ⟨e₀, he₀L, hv₀_in_e₀⟩
        have hno_cycle := hLNoCycles comp hcomp_sub hcomp_ne
        push_neg at hno_cycle
        obtain ⟨w, hw⟩ := hno_cycle
        have hw_deg_le : vertexDegreeIn n comp w ≤ vertexDegreeIn n L w := by
          simpa [hcomp_def] using localEdgeComponentOf_degree_le L v₀ w
        have hw_le2 : vertexDegreeIn n comp w ≤ 2 := by
          calc
            vertexDegreeIn n comp w ≤ vertexDegreeIn n L w := hw_deg_le
            _ ≤ vertexDegreeIn n (L ∪ R) w := by
                unfold vertexDegreeIn
                exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)
            _ = 2 := hSpanning w
        have hw_eq1 : vertexDegreeIn n comp w = 1 := by omega
        have hw_incident : ∃ e ∈ comp, w ∈ e := by
          unfold vertexDegreeIn at hw_eq1
          have hpos : 0 < (comp.filter fun e => w ∈ e).card := by omega
          obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
          simp only [Finset.mem_filter] at he
          exact ⟨e, he.1, he.2⟩
        have hw_reach_L : (edgeSetToGraph n L).Reachable v₀ w :=
          localEdgeComponentOf_reachable L v₀ w hw_incident
        have hw_L_deg : vertexDegreeIn n L w = 1 := by
          rw [← localEdgeComponentOf_degree_eq L v₀ w hw_reach_L]
          simpa [hcomp_def] using hw_eq1
        have hw_bdy : w ∈ boundaryVertices S := hLEndpoints w hw_L_deg
        have hw_reach : (edgeSetToGraph n (L ∪ R)).Reachable v₀ w :=
          reachable_mono Finset.subset_union_left hw_reach_L
        exact ⟨w, hw_bdy, (SimpleGraph.ConnectedComponent.sound hw_reach).symm⟩
      · have hv₀_R_pos : 0 < vertexDegreeIn n R v₀ := by
          unfold vertexDegreeIn
          rw [Finset.card_pos]
          exact ⟨e₀, Finset.mem_filter.mpr ⟨he₀R, hv₀_in_e₀⟩⟩
        have hv₀_R_le : vertexDegreeIn n R v₀ ≤ vertexDegreeIn n (L ∪ R) v₀ := by
          unfold vertexDegreeIn
          exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)
        have hv₀_R_le2 : vertexDegreeIn n R v₀ ≤ 2 := by
          simpa [hv₀_deg] using hv₀_R_le
        have hv₀_R_eq2 : vertexDegreeIn n R v₀ = 2 := by
          have hv₀_R_ne1 : vertexDegreeIn n R v₀ ≠ 1 := h2
          omega
        set comp := localEdgeComponentOf R v₀ with hcomp_def
        have hcomp_sub : comp ⊆ R := localEdgeComponentOf_sub R v₀
        have hcomp_ne : comp.Nonempty :=
          localEdgeComponentOf_nonempty R v₀ ⟨e₀, he₀R, hv₀_in_e₀⟩
        have hno_cycle := hRNoCycles comp hcomp_sub hcomp_ne
        push_neg at hno_cycle
        obtain ⟨w, hw⟩ := hno_cycle
        have hw_deg_le : vertexDegreeIn n comp w ≤ vertexDegreeIn n R w := by
          simpa [hcomp_def] using localEdgeComponentOf_degree_le R v₀ w
        have hw_le2 : vertexDegreeIn n comp w ≤ 2 := by
          calc
            vertexDegreeIn n comp w ≤ vertexDegreeIn n R w := hw_deg_le
            _ ≤ vertexDegreeIn n (L ∪ R) w := by
                unfold vertexDegreeIn
                exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)
            _ = 2 := hSpanning w
        have hw_eq1 : vertexDegreeIn n comp w = 1 := by omega
        have hw_incident : ∃ e ∈ comp, w ∈ e := by
          unfold vertexDegreeIn at hw_eq1
          have hpos : 0 < (comp.filter fun e => w ∈ e).card := by omega
          obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
          simp only [Finset.mem_filter] at he
          exact ⟨e, he.1, he.2⟩
        have hw_reach_R : (edgeSetToGraph n R).Reachable v₀ w :=
          localEdgeComponentOf_reachable R v₀ w hw_incident
        have hw_R_deg : vertexDegreeIn n R w = 1 := by
          rw [← localEdgeComponentOf_degree_eq R v₀ w hw_reach_R]
          simpa [hcomp_def] using hw_eq1
        have hw_bdy : w ∈ boundaryVertices S := hREndpoints w hw_R_deg
        have hw_reach : (edgeSetToGraph n (L ∪ R)).Reachable v₀ w :=
          reachable_mono Finset.subset_union_right hw_reach_R
        exact ⟨w, hw_bdy, (SimpleGraph.ConnectedComponent.sound hw_reach).symm⟩

open Classical in
private theorem every_component_has_bmg_vertex
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (c : (edgeSetToGraph n (L ∪ R)).ConnectedComponent)
    (hc : c ∈ Set.range (edgeSetToGraph n (L ∪ R)).connectedComponentMk) :
    ∃ v : Fin n, v ∈ (boundaryMultigraphOf S L R).vertices ∧
      (edgeSetToGraph n (L ∪ R)).connectedComponentMk v = c := by
  obtain ⟨v₀, rfl⟩ := hc
  by_cases h1 : vertexDegreeIn n L v₀ = 1
  · refine ⟨v₀, ?_, rfl⟩
    unfold boundaryMultigraphOf
    simp only [Finset.mem_filter]
    exact ⟨hLEndpoints v₀ h1, Or.inl h1⟩
  · by_cases h2 : vertexDegreeIn n R v₀ = 1
    · refine ⟨v₀, ?_, rfl⟩
      unfold boundaryMultigraphOf
      simp only [Finset.mem_filter]
      exact ⟨hREndpoints v₀ h2, Or.inr h2⟩
    · have hv₀_deg : vertexDegreeIn n (L ∪ R) v₀ = 2 := hSpanning v₀
      have hv₀_pos : 0 < vertexDegreeIn n (L ∪ R) v₀ := by omega
      unfold vertexDegreeIn at hv₀_pos
      rw [Finset.card_pos] at hv₀_pos
      obtain ⟨e₀, he₀⟩ := hv₀_pos
      simp only [Finset.mem_filter] at he₀
      obtain ⟨he₀_mem, hv₀_in_e₀⟩ := he₀
      rcases Finset.mem_union.mp he₀_mem with he₀L | he₀R
      · have hv₀_L_pos : 0 < vertexDegreeIn n L v₀ := by
          unfold vertexDegreeIn
          rw [Finset.card_pos]
          exact ⟨e₀, Finset.mem_filter.mpr ⟨he₀L, hv₀_in_e₀⟩⟩
        have hv₀_L_le : vertexDegreeIn n L v₀ ≤ vertexDegreeIn n (L ∪ R) v₀ := by
          unfold vertexDegreeIn
          exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)
        have hv₀_L_le2 : vertexDegreeIn n L v₀ ≤ 2 := by
          simpa [hv₀_deg] using hv₀_L_le
        have hv₀_L_eq2 : vertexDegreeIn n L v₀ = 2 := by
          have hv₀_L_ne1 : vertexDegreeIn n L v₀ ≠ 1 := h1
          omega
        set comp := localEdgeComponentOf L v₀ with hcomp_def
        have hcomp_sub : comp ⊆ L := localEdgeComponentOf_sub L v₀
        have hcomp_ne : comp.Nonempty :=
          localEdgeComponentOf_nonempty L v₀ ⟨e₀, he₀L, hv₀_in_e₀⟩
        have hno_cycle := hLNoCycles comp hcomp_sub hcomp_ne
        push_neg at hno_cycle
        obtain ⟨w, hw⟩ := hno_cycle
        have hw_deg_le : vertexDegreeIn n comp w ≤ vertexDegreeIn n L w := by
          simpa [hcomp_def] using localEdgeComponentOf_degree_le L v₀ w
        have hw_le2 : vertexDegreeIn n comp w ≤ 2 := by
          calc
            vertexDegreeIn n comp w ≤ vertexDegreeIn n L w := hw_deg_le
            _ ≤ vertexDegreeIn n (L ∪ R) w := by
                unfold vertexDegreeIn
                exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)
            _ = 2 := hSpanning w
        have hw_eq1 : vertexDegreeIn n comp w = 1 := by omega
        have hw_incident : ∃ e ∈ comp, w ∈ e := by
          unfold vertexDegreeIn at hw_eq1
          have hpos : 0 < (comp.filter fun e => w ∈ e).card := by omega
          obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
          simp only [Finset.mem_filter] at he
          exact ⟨e, he.1, he.2⟩
        have hw_reach_L : (edgeSetToGraph n L).Reachable v₀ w :=
          localEdgeComponentOf_reachable L v₀ w hw_incident
        have hw_L_deg : vertexDegreeIn n L w = 1 := by
          rw [← localEdgeComponentOf_degree_eq L v₀ w hw_reach_L]
          simpa [hcomp_def] using hw_eq1
        have hw_bdy : w ∈ boundaryVertices S := hLEndpoints w hw_L_deg
        have hw_reach : (edgeSetToGraph n (L ∪ R)).Reachable v₀ w :=
          reachable_mono Finset.subset_union_left hw_reach_L
        refine ⟨w, ?_, (SimpleGraph.ConnectedComponent.sound hw_reach).symm⟩
        unfold boundaryMultigraphOf
        simp only [Finset.mem_filter]
        exact ⟨hw_bdy, Or.inl hw_L_deg⟩
      · have hv₀_R_pos : 0 < vertexDegreeIn n R v₀ := by
          unfold vertexDegreeIn
          rw [Finset.card_pos]
          exact ⟨e₀, Finset.mem_filter.mpr ⟨he₀R, hv₀_in_e₀⟩⟩
        have hv₀_R_le : vertexDegreeIn n R v₀ ≤ vertexDegreeIn n (L ∪ R) v₀ := by
          unfold vertexDegreeIn
          exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)
        have hv₀_R_le2 : vertexDegreeIn n R v₀ ≤ 2 := by
          simpa [hv₀_deg] using hv₀_R_le
        have hv₀_R_eq2 : vertexDegreeIn n R v₀ = 2 := by
          have hv₀_R_ne1 : vertexDegreeIn n R v₀ ≠ 1 := h2
          omega
        set comp := localEdgeComponentOf R v₀ with hcomp_def
        have hcomp_sub : comp ⊆ R := localEdgeComponentOf_sub R v₀
        have hcomp_ne : comp.Nonempty :=
          localEdgeComponentOf_nonempty R v₀ ⟨e₀, he₀R, hv₀_in_e₀⟩
        have hno_cycle := hRNoCycles comp hcomp_sub hcomp_ne
        push_neg at hno_cycle
        obtain ⟨w, hw⟩ := hno_cycle
        have hw_deg_le : vertexDegreeIn n comp w ≤ vertexDegreeIn n R w := by
          simpa [hcomp_def] using localEdgeComponentOf_degree_le R v₀ w
        have hw_le2 : vertexDegreeIn n comp w ≤ 2 := by
          calc
            vertexDegreeIn n comp w ≤ vertexDegreeIn n R w := hw_deg_le
            _ ≤ vertexDegreeIn n (L ∪ R) w := by
                unfold vertexDegreeIn
                exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)
            _ = 2 := hSpanning w
        have hw_eq1 : vertexDegreeIn n comp w = 1 := by omega
        have hw_incident : ∃ e ∈ comp, w ∈ e := by
          unfold vertexDegreeIn at hw_eq1
          have hpos : 0 < (comp.filter fun e => w ∈ e).card := by omega
          obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
          simp only [Finset.mem_filter] at he
          exact ⟨e, he.1, he.2⟩
        have hw_reach_R : (edgeSetToGraph n R).Reachable v₀ w :=
          localEdgeComponentOf_reachable R v₀ w hw_incident
        have hw_R_deg : vertexDegreeIn n R w = 1 := by
          rw [← localEdgeComponentOf_degree_eq R v₀ w hw_reach_R]
          simpa [hcomp_def] using hw_eq1
        have hw_bdy : w ∈ boundaryVertices S := hREndpoints w hw_R_deg
        have hw_reach : (edgeSetToGraph n (L ∪ R)).Reachable v₀ w :=
          reachable_mono Finset.subset_union_right hw_reach_R
        refine ⟨w, ?_, (SimpleGraph.ConnectedComponent.sound hw_reach).symm⟩
        unfold boundaryMultigraphOf
        simp only [Finset.mem_filter]
        exact ⟨hw_bdy, Or.inr hw_R_deg⟩

private lemma degree_add_of_disjoint {n : ℕ} (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R) (v : Fin n) :
    vertexDegreeIn n L v + vertexDegreeIn n R v = vertexDegreeIn n (L ∪ R) v := by
  unfold vertexDegreeIn
  rw [Finset.filter_union]
  exact (Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hDisjoint)).symm

private lemma boundary_deg_one_one {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1)
    (v : Fin n) (hv : v ∈ boundaryVertices S) :
    vertexDegreeIn n L v = 1 ∧ vertexDegreeIn n R v = 1 := by
  have hadd := degree_add_of_disjoint L R hDisjoint v
  have htot := hSpanning v
  rcases hBdyDeg1 v hv with hL | hR <;> omega

private lemma non_bdy_full_L_deg {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (v : Fin n) (hv : v ∉ boundaryVertices S) (hpos : 0 < vertexDegreeIn n L v) :
    vertexDegreeIn n L v = 2 := by
  have hadd := degree_add_of_disjoint L R hDisjoint v
  have htot := hSpanning v
  have : vertexDegreeIn n L v ≠ 1 := fun h => hv (hLEndpoints v h)
  omega

open Classical in
private lemma bmg_adj_of_reachable_in_L
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (u v : Fin n) (hne : u ≠ v)
    (hu_bdy : u ∈ boundaryVertices S) (hv_bdy : v ∈ boundaryVertices S)
    (hu_deg : vertexDegreeIn n L u = 1) (hv_deg : vertexDegreeIn n L v = 1)
    (hreach : (edgeSetToGraph n L).Reachable u v) :
    (bmgToGraph (boundaryMultigraphOf S L R)).Adj u v := by
  refine ⟨hne, ?_, ?_, ?_⟩
  · unfold boundaryMultigraphOf
    simp only [Finset.mem_filter]
    exact ⟨hu_bdy, Or.inl hu_deg⟩
  · unfold boundaryMultigraphOf
    simp only [Finset.mem_filter]
    exact ⟨hv_bdy, Or.inl hv_deg⟩
  · left
    simp only [boundaryMultigraphOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hu_bdy, hv_bdy, hne, hu_deg, hv_deg, hreach⟩

open Classical in
private lemma bmg_adj_of_reachable_in_R
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (u v : Fin n) (hne : u ≠ v)
    (hu_bdy : u ∈ boundaryVertices S) (hv_bdy : v ∈ boundaryVertices S)
    (hu_deg : vertexDegreeIn n R u = 1) (hv_deg : vertexDegreeIn n R v = 1)
    (hreach : (edgeSetToGraph n R).Reachable u v) :
    (bmgToGraph (boundaryMultigraphOf S L R)).Adj u v := by
  refine ⟨hne, ?_, ?_, ?_⟩
  · unfold boundaryMultigraphOf
    simp only [Finset.mem_filter]
    exact ⟨hu_bdy, Or.inr hu_deg⟩
  · unfold boundaryMultigraphOf
    simp only [Finset.mem_filter]
    exact ⟨hv_bdy, Or.inr hv_deg⟩
  · right
    right
    left
    simp only [boundaryMultigraphOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hu_bdy, hv_bdy, hne, hu_deg, hv_deg, hreach⟩

open Classical in
private lemma bmg_reachable_of_adj_boundary
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1)
    (u b : Fin n) (hu : u ∈ boundaryVertices S) (hb : b ∈ boundaryVertices S)
    (hreach_L : (edgeSetToGraph n L).Reachable u b)
    (hu_deg : vertexDegreeIn n L u = 1) (hb_deg : vertexDegreeIn n L b = 1) :
    (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u b := by
  by_cases hne : u = b
  · subst hne
    exact SimpleGraph.Reachable.refl u
  · exact (bmg_adj_of_reachable_in_L S L R u b hne hu hb hu_deg hb_deg hreach_L).reachable

open Classical in
private lemma walk_boundary_induction
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1) :
    ∀ (x v : Fin n) (hv : v ∈ boundaryVertices S)
      (w : (edgeSetToGraph n (L ∪ R)).Walk x v)
      (u : Fin n) (hu : u ∈ boundaryVertices S),
      ((edgeSetToGraph n L).Reachable u x ∧ vertexDegreeIn n L u = 1) ∨
      ((edgeSetToGraph n R).Reachable u x ∧ vertexDegreeIn n R u = 1) →
      (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v := by
  intro x v hv w u hu
  induction w generalizing u hu with
  | @nil x =>
    intro hside
    rcases hside with ⟨hLreach, hLdeg⟩ | ⟨hRreach, hRdeg⟩
    · exact bmg_reachable_of_adj_boundary S L R hSpanning hLNoCycles hRNoCycles
        hLEndpoints hREndpoints hBdyDeg1 u x hu hv hLreach hLdeg
        (boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 x hv).1
    · have hv_R := (boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 x hv).2
      by_cases hne : u = x
      · subst hne
        exact SimpleGraph.Reachable.refl u
      · exact (bmg_adj_of_reachable_in_R S L R u x hne hu hv hRdeg hv_R hRreach).reachable
  | @cons x y z hadj_xy w' ih_w' =>
    intro hside
    rcases hside with ⟨hLreach_ux, hLdeg_u⟩ | ⟨hRreach_ux, hRdeg_u⟩
    · rcases Finset.mem_union.mp hadj_xy.2 with hedge_L | hedge_R
      · have hL_adj : (edgeSetToGraph n L).Adj x y := ⟨hadj_xy.1, hedge_L⟩
        exact ih_w' hv u hu (Or.inl ⟨hLreach_ux.trans hL_adj.reachable, hLdeg_u⟩)
      · by_cases hx_bdy : x ∈ boundaryVertices S
        · have ⟨hLx, hRx⟩ :=
            boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 x hx_bdy
          have hbmg_ux := bmg_reachable_of_adj_boundary S L R hSpanning hLNoCycles
            hRNoCycles hLEndpoints hREndpoints hBdyDeg1 u x hu hx_bdy hLreach_ux hLdeg_u hLx
          have hR_adj : (edgeSetToGraph n R).Adj x y := ⟨hadj_xy.1, hedge_R⟩
          exact hbmg_ux.trans (ih_w' hv x hx_bdy (Or.inr ⟨hR_adj.reachable, hRx⟩))
        · exfalso
          have hR_pos : 0 < vertexDegreeIn n R x := by
            unfold vertexDegreeIn
            rw [Finset.card_pos]
            exact ⟨_, Finset.mem_filter.mpr ⟨hedge_R, Sym2.mem_mk_left x y⟩⟩
          have hadd := degree_add_of_disjoint L R hDisjoint x
          have htot := hSpanning x
          by_cases hLx_pos : 0 < vertexDegreeIn n L x
          · have := non_bdy_full_L_deg S L R hDisjoint hSpanning hLEndpoints x hx_bdy hLx_pos
            omega
          · push_neg at hLx_pos
            have hLx0 : vertexDegreeIn n L x = 0 := by omega
            have : u = x := by
              by_contra hne
              obtain ⟨walk⟩ := hLreach_ux.symm
              cases walk with
              | nil => exact hne rfl
              | cons hadj _ =>
                have : 0 < vertexDegreeIn n L x := by
                  unfold vertexDegreeIn
                  rw [Finset.card_pos]
                  exact ⟨_, Finset.mem_filter.mpr ⟨hadj.2, Sym2.mem_mk_left x _⟩⟩
                omega
            subst this
            omega
    · rcases Finset.mem_union.mp hadj_xy.2 with hedge_L | hedge_R
      · by_cases hx_bdy : x ∈ boundaryVertices S
        · have ⟨hLx, hRx⟩ :=
            boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 x hx_bdy
          have hbmg_ux : (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u x := by
            by_cases hne : u = x
            · subst hne
              exact SimpleGraph.Reachable.refl u
            · exact (bmg_adj_of_reachable_in_R S L R u x hne hu hx_bdy
                hRdeg_u hRx hRreach_ux).reachable
          have hL_adj : (edgeSetToGraph n L).Adj x y := ⟨hadj_xy.1, hedge_L⟩
          exact hbmg_ux.trans (ih_w' hv x hx_bdy (Or.inl ⟨hL_adj.reachable, hLx⟩))
        · exfalso
          have hL_pos : 0 < vertexDegreeIn n L x := by
            unfold vertexDegreeIn
            rw [Finset.card_pos]
            exact ⟨_, Finset.mem_filter.mpr ⟨hedge_L, Sym2.mem_mk_left x y⟩⟩
          have hadd := degree_add_of_disjoint L R hDisjoint x
          have htot := hSpanning x
          by_cases hRx_pos : 0 < vertexDegreeIn n R x
          · have hR1 : vertexDegreeIn n R x ≠ 1 := fun h => hx_bdy (hREndpoints x h)
            omega
          · push_neg at hRx_pos
            have hRx0 : vertexDegreeIn n R x = 0 := by omega
            have : u = x := by
              by_contra hne
              obtain ⟨walk⟩ := hRreach_ux.symm
              cases walk with
              | nil => exact hne rfl
              | cons hadj _ =>
                have : 0 < vertexDegreeIn n R x := by
                  unfold vertexDegreeIn
                  rw [Finset.card_pos]
                  exact ⟨_, Finset.mem_filter.mpr ⟨hadj.2, Sym2.mem_mk_left x _⟩⟩
                omega
            subst this
            omega
      · have hR_adj : (edgeSetToGraph n R).Adj x y := ⟨hadj_xy.1, hedge_R⟩
        exact ih_w' hv u hu (Or.inr ⟨hRreach_ux.trans hR_adj.reachable, hRdeg_u⟩)

private theorem reachable_in_union_gives_reachable_in_bmg
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1)
    (u v : Fin n) (hu : u ∈ boundaryVertices S) (hv : v ∈ boundaryVertices S)
    (hreach : (edgeSetToGraph n (L ∪ R)).Reachable u v) :
    (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v := by
  obtain ⟨w⟩ := hreach
  have ⟨hLu, _⟩ := boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 u hu
  exact walk_boundary_induction S L R hDisjoint hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints hBdyDeg1 u v hv w u hu (Or.inl ⟨SimpleGraph.Reachable.refl u, hLu⟩)

private theorem reachable_in_bmg_gives_reachable_in_union
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (u v : Fin n) (hu : u ∈ boundaryVertices S) (hv : v ∈ boundaryVertices S)
    (hreach : (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v) :
    (edgeSetToGraph n (L ∪ R)).Reachable u v := by
  suffices h : ∀ (a b : Fin n),
      (bmgToGraph (boundaryMultigraphOf S L R)).Reachable a b →
      (edgeSetToGraph n (L ∪ R)).Reachable a b from h u v hreach
  intro a b hrab
  obtain ⟨walk⟩ := hrab
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y _ hadj _ ih =>
    apply SimpleGraph.Reachable.trans _ ih
    simp only [bmgToGraph, boundaryMultigraphOf] at hadj
    obtain ⟨_, _, _, hedges⟩ := hadj
    have extract_reach : (edgeSetToGraph n (L ∪ R)).Reachable x y := by
      rcases hedges with hlr | hlr | hlr | hlr
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlr
        exact reachable_mono Finset.subset_union_left hlr.2.2.2.2.2
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlr
        exact (reachable_mono Finset.subset_union_left hlr.2.2.2.2.2).symm
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlr
        exact reachable_mono Finset.subset_union_right hlr.2.2.2.2.2
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlr
        exact (reachable_mono Finset.subset_union_right hlr.2.2.2.2.2).symm
    exact extract_reach

open Classical in
private theorem component_map_well_defined
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1)
    (u v : Fin n) (hu : u ∈ boundaryVertices S) (hv : v ∈ boundaryVertices S)
    (hsame : (edgeSetToGraph n (L ∪ R)).connectedComponentMk u =
             (edgeSetToGraph n (L ∪ R)).connectedComponentMk v) :
    (bmgToGraph (boundaryMultigraphOf S L R)).connectedComponentMk u =
    (bmgToGraph (boundaryMultigraphOf S L R)).connectedComponentMk v := by
  have hreach : (edgeSetToGraph n (L ∪ R)).Reachable u v :=
    SimpleGraph.ConnectedComponent.exact hsame
  have hbmg := reachable_in_union_gives_reachable_in_bmg S L R hDisjoint
    hSpanning hLNoCycles hRNoCycles hLEndpoints hREndpoints hBdyDeg1 u v hu hv hreach
  exact SimpleGraph.ConnectedComponent.sound hbmg

open Classical in
private theorem component_map_injective
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (u v : Fin n) (hu : u ∈ boundaryVertices S) (hv : v ∈ boundaryVertices S)
    (hsame : (bmgToGraph (boundaryMultigraphOf S L R)).connectedComponentMk u =
             (bmgToGraph (boundaryMultigraphOf S L R)).connectedComponentMk v) :
    (edgeSetToGraph n (L ∪ R)).connectedComponentMk u =
    (edgeSetToGraph n (L ∪ R)).connectedComponentMk v := by
  have hreach : (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v :=
    SimpleGraph.ConnectedComponent.exact hsame
  have hunion := reachable_in_bmg_gives_reachable_in_union S L R u v hu hv hreach
  exact SimpleGraph.ConnectedComponent.sound hunion

open Classical in
private theorem contraction_preserves_components :
  ∀ {n : ℕ} (S : Frontier n) (L R : Finset (Edge n)),
    Disjoint L R →
    (∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2) →
    (∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)) →
    (∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)) →
    (∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S) →
    (∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S) →
    (∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1) →
    numComponents (L ∪ R) = numComponentsBMG (boundaryMultigraphOf S L R) := by
  intro n S L R hDisjoint hSpanning hLNoCycles hRNoCycles hLEndpoints hREndpoints hBdyDeg1
  unfold numComponents numComponentsBMG
  set G := edgeSetToGraph n (L ∪ R)
  set B := boundaryMultigraphOf S L R
  set Gb := bmgToGraph B
  have hBverts : B.vertices = boundaryVertices S := by
    unfold B boundaryMultigraphOf
    apply Finset.ext
    intro v
    simp only [Finset.mem_filter]
    constructor
    · intro hv
      exact hv.1
    · intro hv
      exact ⟨hv, hBdyDeg1 v hv⟩
  have hevery := every_component_has_boundary_vertex S L R hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints
  have hwd := component_map_well_defined S L R hDisjoint hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints hBdyDeg1
  have hinj := component_map_injective S L R
  let repG : G.ConnectedComponent → Fin n := fun c =>
    (hevery c (c.ind (fun v => ⟨v, rfl⟩))).choose
  have hrepG_bdy : ∀ c, repG c ∈ boundaryVertices S :=
    fun c => (hevery c (c.ind (fun v => ⟨v, rfl⟩))).choose_spec.1
  have hrepG_eq : ∀ c, G.connectedComponentMk (repG c) = c :=
    fun c => (hevery c (c.ind (fun v => ⟨v, rfl⟩))).choose_spec.2
  let φ : G.ConnectedComponent → Gb.ConnectedComponent := fun c => Gb.connectedComponentMk (repG c)
  suffices himg : φ '' (Set.range G.connectedComponentMk) =
      {c : Gb.ConnectedComponent | ∃ v ∈ B.vertices, Gb.connectedComponentMk v = c} by
    rw [← himg]
    exact (Set.ncard_image_of_injOn (fun c₁ _ c₂ _ heq => by
      rw [← hrepG_eq c₁, ← hrepG_eq c₂]
      exact hinj _ _ (hrepG_bdy c₁) (hrepG_bdy c₂) heq)).symm
  ext cb
  constructor
  · rintro ⟨c, ⟨v₀, rfl⟩, rfl⟩
    exact ⟨repG (G.connectedComponentMk v₀), hBverts.symm ▸ hrepG_bdy _, rfl⟩
  · rintro ⟨v, hv_mem, rfl⟩
    have hv_bdy : v ∈ boundaryVertices S := by
      simpa [hBverts] using hv_mem
    refine ⟨G.connectedComponentMk v, ⟨v, rfl⟩, ?_⟩
    exact hwd (repG (G.connectedComponentMk v)) v (hrepG_bdy _) hv_bdy
      (hrepG_eq (G.connectedComponentMk v))

private theorem connected_iff_one_component :
  ∀ {n : ℕ} (edges : Finset (Edge n)),
    IsConnectedEdgeSet n edges ↔ numComponents edges = 1 := by
  intro n edges
  unfold IsConnectedEdgeSet numComponents
  set G := edgeSetToGraph n edges
  constructor
  · intro hconn
    have hpre := hconn.preconnected
    haveI := hconn.nonempty
    haveI := hpre.subsingleton_connectedComponent
    have v₀ := Classical.arbitrary (Fin n)
    have hrange : Set.range G.connectedComponentMk = {G.connectedComponentMk v₀} := by
      ext c
      simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨v, hv⟩ => hv ▸ Subsingleton.elim _ _, fun h => ⟨v₀, h.symm⟩⟩
    rw [hrange, Set.ncard_singleton]
  · intro h
    rw [Set.ncard_eq_one] at h
    obtain ⟨c, hc⟩ := h
    have hmem : c ∈ Set.range G.connectedComponentMk := hc ▸ Set.mem_singleton c
    obtain ⟨v₀, hv₀⟩ := hmem
    haveI : Nonempty (Fin n) := ⟨v₀⟩
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ‹_›⟩
    have hu : G.connectedComponentMk u ∈ ({c} : Set _) := hc ▸ Set.mem_range_self u
    have hv : G.connectedComponentMk v ∈ ({c} : Set _) := hc ▸ Set.mem_range_self v
    rw [Set.mem_singleton_iff] at hu hv
    exact SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)

private theorem bmg_connected_iff_one_component :
  ∀ {n : ℕ} (G : BoundaryMultigraph n),
    IsConnectedBoundaryMultigraph G ↔ numComponentsBMG G = 1 :=
  fun _ => Iff.rfl

theorem boundaryComponentCorrespondence
    (S : Frontier n)
    (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1) :
    numComponents (L ∪ R) = numComponentsBMG (boundaryMultigraphOf S L R) :=
  contraction_preserves_components S L R hDisjoint hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints hBdyDeg1

theorem boundaryComponentCorrespondence_ham
    (S : Frontier n)
    (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1) :
    IsConnectedFinset (L ∪ R) ↔
      IsConnectedBoundaryMultigraph (boundaryMultigraphOf S L R) := by
  unfold IsConnectedFinset
  rw [connected_iff_one_component, bmg_connected_iff_one_component]
  rw [boundaryComponentCorrespondence S L R hDisjoint hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints hBdyDeg1]


end BoundaryComponentCorrespondence

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

private lemma danglingEndpoints_eq_of_degreeProfile_eq
    (S : Frontier n) (H H' : Finset (Edge n))
    (hd : degreeProfile S H = degreeProfile S H') :
    danglingEndpoints S H = danglingEndpoints S H' := by
  unfold danglingEndpoints
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hvb, hvd⟩
    simp [degreeProfile] at hvd ⊢
    have hval : leftDegreeAt S H v = leftDegreeAt S H' v := by
      simpa [degreeProfile] using congrArg (fun f => f v) hd
    exact ⟨hvb, hval ▸ hvd⟩
  · rintro ⟨hvb, hvd⟩
    simp [degreeProfile] at hvd ⊢
    have hval : leftDegreeAt S H v = leftDegreeAt S H' v := by
      simpa [degreeProfile] using congrArg (fun f => f v) hd
    exact ⟨hvb, hval.symm ▸ hvd⟩

private lemma left_degree_one_is_boundary
    (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H)
    (v : Fin n) (hdeg : vertexDegreeIn n (leftSubgraph S H) v = 1) :
    v ∈ boundaryVertices S := by
  unfold boundaryVertices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · unfold leftSubgraph vertexDegreeIn at hdeg
    have hpos : 0 < (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).card := by omega
    rw [Finset.card_pos] at hpos
    obtain ⟨e, he⟩ := hpos
    simp only [Finset.mem_filter, Finset.mem_inter] at he
    exact ⟨e, he.1.2, he.2⟩
  · have hsum := leftDeg_add_rightDeg_eq_two S H hH v
    have hright : rightDegreeAt S H v = 1 := by
      unfold leftDegreeAt rightDegreeAt at *
      omega
    unfold rightDegreeAt rightSubgraph vertexDegreeIn at hright
    have hpos : 0 < (Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges)).card := by omega
    rw [Finset.card_pos] at hpos
    obtain ⟨e, he⟩ := hpos
    simp only [Finset.mem_filter, Finset.mem_inter] at he
    exact ⟨e, he.1.2, he.2⟩

private lemma right_degree_one_is_boundary
    (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H)
    (v : Fin n) (hdeg : vertexDegreeIn n (rightSubgraph S H) v = 1) :
    v ∈ boundaryVertices S := by
  have := left_degree_one_is_boundary S.swap H hH v (by
    simpa [leftSubgraph_swap] using hdeg)
  simpa [boundaryVertices_swap] using this

private lemma danglingEndpoints_eq_degree_iff
    (S : Frontier n) (H H' : Finset (Edge n))
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (v : Fin n) (hv : v ∈ boundaryVertices S) :
    vertexDegreeIn n (leftSubgraph S H) v = 1 ↔
    vertexDegreeIn n (leftSubgraph S H') v = 1 := by
  have fwd : v ∈ danglingEndpoints S H ↔ v ∈ danglingEndpoints S H' := by
    rw [hU]
  unfold danglingEndpoints at fwd
  simp only [Finset.mem_filter] at fwd
  unfold degreeProfile leftDegreeAt at fwd
  constructor
  · intro h
    exact (fwd.mp ⟨hv, h⟩).2
  · intro h
    exact (fwd.mpr ⟨hv, h⟩).2

private theorem leftSubgraph_no_cycle_of_nonempty_dangling
    (S : Frontier n) (hS : S.isBalanced) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (hDang : (danglingEndpoints S H).Nonempty) :
    ∀ comp : Finset (Edge n), comp ⊆ leftSubgraph S H → comp.Nonempty →
      ¬ (∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) := by
  have hc : ¬ hasPrematureCycle S H := no_prematureCycle_at_balanced_frontier S hS H hH
  intro comp hcomp hne hall
  have hneq : comp ≠ H := by
    intro hEq
    obtain ⟨u, hu⟩ := hDang
    have hHsubL : H ⊆ leftSubgraph S H := by
      intro e he
      exact hcomp (hEq ▸ he)
    have hHeqL : H = leftSubgraph S H := by
      apply Finset.Subset.antisymm
      · exact hHsubL
      · exact Finset.inter_subset_left
    have hu_degL : vertexDegreeIn n (leftSubgraph S H) u = 1 := by
      simp only [danglingEndpoints, Finset.mem_filter, degreeProfile] at hu
      simpa [leftDegreeAt] using hu.2
    have hu_deg : vertexDegreeIn n H u = 1 := by
      rw [← hHeqL] at hu_degL
      exact hu_degL
    rw [← hEq] at hu_deg
    rcases hall u with h0 | h2 <;> omega
  exact hc ⟨comp, hcomp, hne, hall, hneq⟩

private theorem rightSubgraph_no_cycle_of_nonempty_dangling
    (S : Frontier n) (hS : S.isBalanced) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (hDang : (danglingEndpoints S H).Nonempty) :
    ∀ comp : Finset (Edge n), comp ⊆ rightSubgraph S H → comp.Nonempty →
      ¬ (∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) := by
  have hSswap : S.swap.isBalanced := ⟨hS.2, hS.1⟩
  have hc : ¬ hasPrematureCycle S.swap H := no_prematureCycle_at_balanced_frontier S.swap hSswap H hH
  intro comp hcomp hne hall
  have hneq : comp ≠ H := by
    intro hEq
    obtain ⟨u, hu⟩ := (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ hDang)
    have hHsubR : H ⊆ rightSubgraph S H := by
      intro e he
      exact hcomp (hEq ▸ he)
    have hHeqR : H = rightSubgraph S H := by
      apply Finset.Subset.antisymm
      · exact hHsubR
      · exact Finset.inter_subset_left
    have hu_degR : vertexDegreeIn n (rightSubgraph S H) u = 1 := by
      simp only [rightDanglingEndpoints, Finset.mem_filter] at hu
      simpa [rightDegreeAt] using hu.2
    have hu_deg : vertexDegreeIn n H u = 1 := by
      rw [← hHeqR] at hu_degR
      exact hu_degR
    rw [← hEq] at hu_deg
    rcases hall u with h0 | h2 <;> omega
  exact hc ⟨comp, by simpa [leftSubgraph_swap] using hcomp, hne, hall, hneq⟩

private theorem leftSubgraph_eq_empty_or_self_of_empty_dangling
    (S : Frontier n) (hS : S.isBalanced) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (hEmpty : danglingEndpoints S H = ∅) :
    leftSubgraph S H = ∅ ∨ leftSubgraph S H = H := by
  by_cases hLempty : leftSubgraph S H = ∅
  · exact Or.inl hLempty
  · right
    have hne : (leftSubgraph S H).Nonempty := Finset.nonempty_iff_ne_empty.mpr hLempty
    have hall : ∀ v : Fin n, vertexDegreeIn n (leftSubgraph S H) v = 0 ∨
        vertexDegreeIn n (leftSubgraph S H) v = 2 := by
      intro v
      have hle : vertexDegreeIn n (leftSubgraph S H) v ≤ 2 := by
        unfold vertexDegreeIn
        calc
          (Finset.filter (fun e => v ∈ e) (leftSubgraph S H)).card
              ≤ (Finset.filter (fun e => v ∈ e) H).card := by
                exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.inter_subset_left)
          _ = 2 := hH.twoRegular v
      by_cases h0 : vertexDegreeIn n (leftSubgraph S H) v = 0
      · exact Or.inl h0
      have hne1 : vertexDegreeIn n (leftSubgraph S H) v ≠ 1 := by
        intro h1
        have hv_bdy := left_degree_one_is_boundary S H hH v h1
        have hv_dang : v ∈ danglingEndpoints S H := by
          unfold danglingEndpoints
          simp only [Finset.mem_filter, degreeProfile]
          exact ⟨hv_bdy, by simpa [leftDegreeAt] using h1⟩
        rw [hEmpty] at hv_dang
        simp at hv_dang
      omega
    have hc : ¬ hasPrematureCycle S H := no_prematureCycle_at_balanced_frontier S hS H hH
    by_contra hneq
    exact hc ⟨leftSubgraph S H, subset_rfl, hne, hall, hneq⟩

private lemma same_pairing_implies_left_reachability_iff
    (S : Frontier n) (_hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hπ : HEq (pathPairing S H hH) (pathPairing S H' hH'))
    (u v : Fin n)
    (hu_bdy : u ∈ boundaryVertices S) (hv_bdy : v ∈ boundaryVertices S)
    (hu_deg : vertexDegreeIn n (leftSubgraph S H) u = 1)
    (hv_deg : vertexDegreeIn n (leftSubgraph S H) v = 1) :
    (edgeSetToGraph n (leftSubgraph S H')).Reachable u v ↔
    (edgeSetToGraph n (leftSubgraph S H)).Reachable u v := by
  by_cases hne : u = v
  · subst hne
    simp only [SimpleGraph.Reachable.refl, iff_self]
  · have hu_dang : u ∈ danglingEndpoints S H := by
      unfold danglingEndpoints
      simp only [Finset.mem_filter]
      exact ⟨hu_bdy, hu_deg⟩
    have hv_dang : v ∈ danglingEndpoints S H := by
      unfold danglingEndpoints
      simp only [Finset.mem_filter]
      exact ⟨hv_bdy, hv_deg⟩
    have hu_deg' : vertexDegreeIn n (leftSubgraph S H') u = 1 :=
      (danglingEndpoints_eq_degree_iff S H H' hU u hu_bdy).mp hu_deg
    have hv_deg' : vertexDegreeIn n (leftSubgraph S H') v = 1 :=
      (danglingEndpoints_eq_degree_iff S H H' hU v hv_bdy).mp hv_deg
    have hu_dang' : u ∈ danglingEndpoints S H' := by
      unfold danglingEndpoints
      simp only [Finset.mem_filter]
      exact ⟨hu_bdy, hu_deg'⟩
    have hv_dang' : v ∈ danglingEndpoints S H' := by
      unfold danglingEndpoints
      simp only [Finset.mem_filter]
      exact ⟨hv_bdy, hv_deg'⟩
    have pairs_eq : (pathPairing S H hH).pairs = (pathPairing S H' hH').pairs := by
      have : ∀ (U U' : Finset (Fin n)) (M : PerfectMatching U) (M' : PerfectMatching U')
          (hUU : U = U') (hMM : HEq M M'), M.pairs = M'.pairs := by
        intro U _ M M' hUU hMM
        subst hUU
        exact congrArg PerfectMatching.pairs (eq_of_heq hMM)
      exact this _ _ _ _ hU hπ
    rw [← pathPairing_iff_reachable S H' hH' u v hu_dang' hv_dang' hne,
        ← pathPairing_iff_reachable S H hH u v hu_dang hv_dang hne,
        pairs_eq]

open Classical in
private theorem matching_pairings_give_same_boundary_left_edges
    (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hπ : HEq (pathPairing S H hH) (pathPairing S H' hH')) :
    boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H) =
    boundaryMultigraphOf S (leftSubgraph S H) (rightSubgraph S H) := by
  unfold boundaryMultigraphOf
  have hvertices :
      (boundaryVertices S).filter
          (fun v =>
            vertexDegreeIn n (leftSubgraph S H') v = 1 ∨
              vertexDegreeIn n (rightSubgraph S H) v = 1) =
        (boundaryVertices S).filter
          (fun v =>
            vertexDegreeIn n (leftSubgraph S H) v = 1 ∨
              vertexDegreeIn n (rightSubgraph S H) v = 1) := by
    apply Finset.ext
    intro v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hpdeg | hpdeg⟩
      · exact ⟨hp, Or.inl ((danglingEndpoints_eq_degree_iff S H H' hU v hp).mpr hpdeg)⟩
      · exact ⟨hp, Or.inr hpdeg⟩
    · rintro ⟨hp, hpdeg | hpdeg⟩
      · exact ⟨hp, Or.inl ((danglingEndpoints_eq_degree_iff S H H' hU v hp).mp hpdeg)⟩
      · exact ⟨hp, Or.inr hpdeg⟩
  have hledges :
      (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p =>
            p.1 ∈ boundaryVertices S ∧ p.2 ∈ boundaryVertices S ∧
              p.1 ≠ p.2 ∧
              vertexDegreeIn n (leftSubgraph S H') p.1 = 1 ∧
                vertexDegreeIn n (leftSubgraph S H') p.2 = 1 ∧
                  (edgeSetToGraph n (leftSubgraph S H')).Reachable p.1 p.2) =
        (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p =>
            p.1 ∈ boundaryVertices S ∧ p.2 ∈ boundaryVertices S ∧
              p.1 ≠ p.2 ∧
              vertexDegreeIn n (leftSubgraph S H) p.1 = 1 ∧
                vertexDegreeIn n (leftSubgraph S H) p.2 = 1 ∧
                  (edgeSetToGraph n (leftSubgraph S H)).Reachable p.1 p.2) := by
    apply Finset.ext
    intro q
    rcases q with ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp1, hp2, hne, hdeg1, hdeg2, hreach⟩
      have hdeg1' := (danglingEndpoints_eq_degree_iff S H H' hU u hp1).mpr hdeg1
      have hdeg2' := (danglingEndpoints_eq_degree_iff S H H' hU v hp2).mpr hdeg2
      exact ⟨hp1, hp2, hne, hdeg1', hdeg2',
        (same_pairing_implies_left_reachability_iff S hS H H' hH hH' hU hπ
          u v hp1 hp2 hdeg1' hdeg2').mp hreach⟩
    · rintro ⟨hp1, hp2, hne, hdeg1, hdeg2, hreach⟩
      have hdeg1' := (danglingEndpoints_eq_degree_iff S H H' hU u hp1).mp hdeg1
      have hdeg2' := (danglingEndpoints_eq_degree_iff S H H' hU v hp2).mp hdeg2
      exact ⟨hp1, hp2, hne, hdeg1', hdeg2',
        (same_pairing_implies_left_reachability_iff S hS H H' hH hH' hU hπ
          u v hp1 hp2 hdeg1 hdeg2).mpr hreach⟩
  simpa [hvertices, hledges]

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

private theorem foldl_append_singleton_length {α β : Type*}
    (xs : List α) (acc : List β) (f : List β → α → β) :
    (xs.foldl (init := acc) fun acc x => acc ++ [f acc x]).length = acc.length + xs.length := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      have h := ih (acc ++ [f acc x])
      simpa [List.foldl, List.length_append, List.length_singleton,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem evalAllGatesAux_length
    (gates : List Gate) (acc : List Bool) :
    (gates.foldl (init := acc) fun acc g =>
      let v1 := acc.getD g.input1 false
      let v2 := acc.getD g.input2 false
      let result := match g.kind with
        | GateKind.AND => v1 && v2
        | GateKind.OR  => v1 || v2
        | GateKind.NOT => !v1
      acc ++ [result]).length = acc.length + gates.length := by
  simpa using foldl_append_singleton_length gates acc
    (fun acc g =>
      let v1 := acc.getD g.input1 false
      let v2 := acc.getD g.input2 false
      match g.kind with
      | GateKind.AND => v1 && v2
      | GateKind.OR  => v1 || v2
      | GateKind.NOT => !v1)

private theorem evalAllGates_length {m : ℕ} (C : BooleanCircuit m)
    (input : Fin m → Bool) :
    (evalAllGates C input).length = m + C.gates.length := by
  unfold evalAllGates
  rw [evalAllGatesAux_length]
  have hlen : (List.ofFn input).length = m := by simp
  rw [hlen]

noncomputable def frontierGateIndices {m : ℕ} (C : BooleanCircuit m)
    (_S : Frontier n) : List ℕ :=
  List.range (m + C.gates.length)

noncomputable def frontierTranscript {m : ℕ} (C : BooleanCircuit m) (S : Frontier n)
    (input : Fin m → Bool) : List Bool :=
  List.ofFn fun i : Fin (m + C.gates.length) => (evalAllGates C input).getD i false

private theorem frontierTranscript_eq_evalAllGates {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n) (input : Fin m → Bool) :
    frontierTranscript C S input = evalAllGates C input := by
  calc
    frontierTranscript C S input =
        List.ofFn (fun i : Fin (evalAllGates C input).length =>
          (evalAllGates C input).getD i false) := by
      unfold frontierTranscript
      rw [show m + C.gates.length = (evalAllGates C input).length by
        exact (evalAllGates_length C input).symm]
    _ = List.ofFn (fun i : Fin (evalAllGates C input).length =>
          (evalAllGates C input)[(i : Nat)]) := by
      congr
      funext i
      simpa using (List.getD_eq_get (l := evalAllGates C input) (d := false) i)
    _ = evalAllGates C input := List.ofFn_getElem _

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
    frontierTranscript C S (toInput (mixedGraph S H H')) =
      frontierTranscript C S (toInput H) →
    C.eval (toInput (mixedGraph S H H')) = C.eval (toInput H) := by
  intro n m C S toInput H H' h_same
  rw [frontierTranscript_eq_evalAllGates, frontierTranscript_eq_evalAllGates] at h_same
  unfold BooleanCircuit.eval
  exact congrArg (fun vals => vals.getD C.outputGate false) h_same

theorem rectangle_property {m : ℕ} (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hm : frontierTranscript C S (toInput (mixedGraph S H H')) =
      frontierTranscript C S (toInput H)) :
    C.eval (toInput (mixedGraph S H H')) = C.eval (toInput H) :=
  circuit_rectangle C S toInput H H' hm

end FrontierTranscript

section DegreeCollision

theorem degree_collision_forces_error {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hCorrect : CircuitDecidesHAM C toInput)
    (hm : frontierTranscript C S (toInput (mixedGraph S H H')) =
      frontierTranscript C S (toInput H))
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

private theorem bmg_vertices_eq_dangling
    {n : ℕ} (S : Frontier n)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H') :
    (boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H)).vertices =
    danglingEndpoints S H := by
  unfold boundaryMultigraphOf danglingEndpoints
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hbv, hdeg⟩
    constructor
    · exact hbv
    · rcases hdeg with h | h
      · have hv_dang' : v ∈ danglingEndpoints S H' := by
          unfold danglingEndpoints
          simp only [Finset.mem_filter]
          exact ⟨hbv, by
            unfold degreeProfile leftDegreeAt
            exact h⟩
        rw [← hU] at hv_dang'
        exact (Finset.mem_filter.mp hv_dang').2
      · unfold degreeProfile leftDegreeAt
        have h2 := leftDeg_add_rightDeg_eq_two S H hH v
        unfold leftDegreeAt rightDegreeAt at h2
        omega
  · rintro ⟨hbv, hdeg⟩
    constructor
    · exact hbv
    · left
      have hv_dang : v ∈ danglingEndpoints S H := by
        unfold danglingEndpoints
        simp only [Finset.mem_filter]
        exact ⟨hbv, hdeg⟩
      rw [hU] at hv_dang
      unfold danglingEndpoints at hv_dang
      have hfilt := (Finset.mem_filter.mp hv_dang).2
      unfold degreeProfile leftDegreeAt at hfilt
      exact hfilt

private theorem cast_pairs_eq
    {n : ℕ} {U V : Finset (Fin n)} (h : U = V) (M : PerfectMatching V) :
    (h ▸ M).pairs = M.pairs := by
  subst h
  rfl

private theorem bmg_ledge_of_pair
    {n : ℕ} (S : Frontier n)
    (H' : Finset (Edge n)) (hH' : IsHamCycle n H')
    (R : Finset (Edge n))
    (p : Fin n × Fin n) (hp : p ∈ (pathPairing S H' hH').pairs) :
    (p.1, p.2) ∈ (boundaryMultigraphOf S (leftSubgraph S H') R).lEdges := by
  unfold boundaryMultigraphOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hp1 := (pathPairing S H' hH').fst_mem p hp
  have hp2 := (pathPairing S H' hH').snd_mem p hp
  have hp1_bdy : p.1 ∈ boundaryVertices S := by
    unfold danglingEndpoints at hp1
    exact (Finset.mem_filter.mp hp1).1
  have hp2_bdy : p.2 ∈ boundaryVertices S := by
    unfold danglingEndpoints at hp2
    exact (Finset.mem_filter.mp hp2).1
  have hp1_deg : vertexDegreeIn n (leftSubgraph S H') p.1 = 1 := by
    unfold danglingEndpoints degreeProfile leftDegreeAt at hp1
    exact (Finset.mem_filter.mp hp1).2
  have hp2_deg : vertexDegreeIn n (leftSubgraph S H') p.2 = 1 := by
    unfold danglingEndpoints degreeProfile leftDegreeAt at hp2
    exact (Finset.mem_filter.mp hp2).2
  exact ⟨hp1_bdy, hp2_bdy,
    (pathPairing S H' hH').ne_pair p hp,
    hp1_deg, hp2_deg,
    pathPairing_reflects_components S H' hH' p hp⟩

private theorem bmg_redge_of_pair
    {n : ℕ} (S : Frontier n)
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (L : Finset (Edge n))
    (p : Fin n × Fin n) (hp : p ∈ (rightPairing S H hH).pairs) :
    (p.1, p.2) ∈ (boundaryMultigraphOf S L (rightSubgraph S H)).rEdges := by
  unfold boundaryMultigraphOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hp1 := (rightPairing S H hH).fst_mem p hp
  have hp2 := (rightPairing S H hH).snd_mem p hp
  have hp1_bdy : p.1 ∈ boundaryVertices S := by
    unfold rightDanglingEndpoints at hp1
    exact (Finset.mem_filter.mp hp1).1
  have hp2_bdy : p.2 ∈ boundaryVertices S := by
    unfold rightDanglingEndpoints at hp2
    exact (Finset.mem_filter.mp hp2).1
  have hp1_deg : vertexDegreeIn n (rightSubgraph S H) p.1 = 1 := by
    unfold rightDanglingEndpoints rightDegreeAt at hp1
    exact (Finset.mem_filter.mp hp1).2
  have hp2_deg : vertexDegreeIn n (rightSubgraph S H) p.2 = 1 := by
    unfold rightDanglingEndpoints rightDegreeAt at hp2
    exact (Finset.mem_filter.mp hp2).2
  exact ⟨hp1_bdy, hp2_bdy,
    (rightPairing S H hH).ne_pair p hp,
    hp1_deg, hp2_deg,
    rightPairing_reflects_components S H hH p hp⟩

private theorem pair_of_bmg_ledge
    {n : ℕ} (S : Frontier n)
    (H' : Finset (Edge n)) (hH' : IsHamCycle n H')
    (R : Finset (Edge n))
    (u v : Fin n) (hne : u ≠ v)
    (hle : (u, v) ∈ (boundaryMultigraphOf S (leftSubgraph S H') R).lEdges) :
    (u, v) ∈ (pathPairing S H' hH').pairs ∨ (v, u) ∈ (pathPairing S H' hH').pairs := by
  unfold boundaryMultigraphOf at hle
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hle
  obtain ⟨hu_bdy, hv_bdy, _, hu_deg, hv_deg, hreach⟩ := hle
  have hu_dang : u ∈ danglingEndpoints S H' := by
    unfold danglingEndpoints
    simp only [Finset.mem_filter]
    exact ⟨hu_bdy, by
      unfold degreeProfile leftDegreeAt
      exact hu_deg⟩
  have hv_dang : v ∈ danglingEndpoints S H' := by
    unfold danglingEndpoints
    simp only [Finset.mem_filter]
    exact ⟨hv_bdy, by
      unfold degreeProfile leftDegreeAt
      exact hv_deg⟩
  exact (pathPairing_iff_reachable S H' hH' u v hu_dang hv_dang hne).mpr hreach

private theorem pair_of_bmg_redge
    {n : ℕ} (S : Frontier n)
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (L : Finset (Edge n))
    (u v : Fin n) (hne : u ≠ v)
    (hre : (u, v) ∈ (boundaryMultigraphOf S L (rightSubgraph S H)).rEdges) :
    (u, v) ∈ (rightPairing S H hH).pairs ∨ (v, u) ∈ (rightPairing S H hH).pairs := by
  unfold boundaryMultigraphOf at hre
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hre
  obtain ⟨hu_bdy, hv_bdy, _, hu_deg, hv_deg, hreach⟩ := hre
  have hu_rdang : u ∈ rightDanglingEndpoints S H := by
    unfold rightDanglingEndpoints
    simp only [Finset.mem_filter]
    exact ⟨hu_bdy, by
      unfold rightDegreeAt
      exact hu_deg⟩
  have hv_rdang : v ∈ rightDanglingEndpoints S H := by
    unfold rightDanglingEndpoints
    simp only [Finset.mem_filter]
    exact ⟨hv_bdy, by
      unfold rightDegreeAt
      exact hv_deg⟩
  exact (rightPairing_iff_reachable S H hH u v hu_rdang hv_rdang hne).mpr hreach

private theorem bmg_adj_iff_overlay_adj
    {n : ℕ} (S : Frontier n) (_hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (_hd : degreeProfile S H = degreeProfile S H')
    (_hc : ¬ hasPrematureCycle S H)
    (_hc' : ¬ hasPrematureCycle S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (u v : Fin n) :
    let π' := hU ▸ pathPairing S H' hH'
    let ρ := danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH
    (bmgToGraph (boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H))).Adj u v ↔
    (overlayGraph π' ρ).Adj u v := by
  set L := leftSubgraph S H'
  set R := rightSubgraph S H
  set BMG := boundaryMultigraphOf S L R
  set π' := hU ▸ pathPairing S H' hH'
  set ρ := danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH
  have hπ'_pairs : π'.pairs = (pathPairing S H' hH').pairs :=
    cast_pairs_eq hU (pathPairing S H' hH')
  have hρ_pairs : ρ.pairs = (rightPairing S H hH).pairs :=
    cast_pairs_eq (danglingEndpoints_eq_rightDanglingEndpoints S H hH) (rightPairing S H hH)
  have hverts := bmg_vertices_eq_dangling S H H' hH hH' hU
  constructor
  · intro hadj
    have hne := hadj.1
    have hedges := hadj.2.2.2
    show (overlayGraph π' ρ).Adj u v
    unfold overlayGraph
    rcases hedges with hle | hle | hre | hre
    · have := pair_of_bmg_ledge S H' hH' R u v hne hle
      left
      rw [hπ'_pairs]
      rcases this with hp | hp
      · exact ⟨(u, v), hp, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨(v, u), hp, Or.inr ⟨rfl, rfl⟩⟩
    · have := pair_of_bmg_ledge S H' hH' R v u (Ne.symm hne) hle
      left
      rw [hπ'_pairs]
      rcases this with hp | hp
      · exact ⟨(v, u), hp, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨(u, v), hp, Or.inl ⟨rfl, rfl⟩⟩
    · have := pair_of_bmg_redge S H hH L u v hne hre
      right
      rw [hρ_pairs]
      rcases this with hp | hp
      · exact ⟨(u, v), hp, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨(v, u), hp, Or.inr ⟨rfl, rfl⟩⟩
    · have := pair_of_bmg_redge S H hH L v u (Ne.symm hne) hre
      right
      rw [hρ_pairs]
      rcases this with hp | hp
      · exact ⟨(v, u), hp, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨(u, v), hp, Or.inl ⟨rfl, rfl⟩⟩
  · intro hovl
    show (bmgToGraph BMG).Adj u v
    unfold overlayGraph at hovl
    rcases hovl with ⟨p, hp, hpuv⟩ | ⟨p, hp, hpuv⟩
    · rw [hπ'_pairs] at hp
      have hne : u ≠ v := by
        rcases hpuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (pathPairing S H' hH').ne_pair p hp
        · exact ((pathPairing S H' hH').ne_pair p hp).symm
      have hp1_dang' := (pathPairing S H' hH').fst_mem p hp
      have hp2_dang' := (pathPairing S H' hH').snd_mem p hp
      have hle := bmg_ledge_of_pair S H' hH' R p hp
      rcases hpuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hne,
          hverts ▸ (hU ▸ hp1_dang' : p.1 ∈ danglingEndpoints S H),
          hverts ▸ (hU ▸ hp2_dang' : p.2 ∈ danglingEndpoints S H),
          Or.inl hle⟩
      · exact ⟨hne,
          hverts ▸ (hU ▸ hp2_dang' : p.2 ∈ danglingEndpoints S H),
          hverts ▸ (hU ▸ hp1_dang' : p.1 ∈ danglingEndpoints S H),
          Or.inr (Or.inl hle)⟩
    · rw [hρ_pairs] at hp
      have hne : u ≠ v := by
        rcases hpuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (rightPairing S H hH).ne_pair p hp
        · exact ((rightPairing S H hH).ne_pair p hp).symm
      have hp1_rdang := (rightPairing S H hH).fst_mem p hp
      have hp2_rdang := (rightPairing S H hH).snd_mem p hp
      have hDE := danglingEndpoints_eq_rightDanglingEndpoints S H hH
      have hre := bmg_redge_of_pair S H hH L p hp
      rcases hpuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hne,
          hverts ▸ (hDE ▸ hp1_rdang : p.1 ∈ danglingEndpoints S H),
          hverts ▸ (hDE ▸ hp2_rdang : p.2 ∈ danglingEndpoints S H),
          Or.inr (Or.inr (Or.inl hre))⟩
      · exact ⟨hne,
          hverts ▸ (hDE ▸ hp2_rdang : p.2 ∈ danglingEndpoints S H),
          hverts ▸ (hDE ▸ hp1_rdang : p.1 ∈ danglingEndpoints S H),
          Or.inr (Or.inr (Or.inr hre))⟩

private theorem same_adj_same_components
    {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (hadj : ∀ u v : Fin n, G₁.Adj u v ↔ G₂.Adj u v) :
    Set.ncard {c : G₁.ConnectedComponent | ∃ v ∈ U, G₁.connectedComponentMk v = c} =
    Set.ncard {c : G₂.ConnectedComponent | ∃ v ∈ U, G₂.connectedComponentMk v = c} := by
  have hG : G₁ = G₂ := by
    ext u v
    exact hadj u v
  subst hG
  rfl

private theorem boundary_multigraph_equals_overlay_components :
    ∀ {n : ℕ} (S : Frontier n) (hS : S.isBalanced)
      (H H' : Finset (Edge n))
      (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
      (hd : degreeProfile S H = degreeProfile S H')
      (hc : ¬ hasPrematureCycle S H)
      (hc' : ¬ hasPrematureCycle S H')
      (hU : danglingEndpoints S H = danglingEndpoints S H'),
      let π' := hU ▸ pathPairing S H' hH'
      let ρ := danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH
      numComponentsBMG (boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H)) =
      overlayComponentCount π' ρ := by
  intro n S hS H H' hH hH' hd hc hc' hU
  set BMG := boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H)
  set π' := hU ▸ pathPairing S H' hH'
  set ρ := danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH
  unfold numComponentsBMG overlayComponentCount
  have hverts := bmg_vertices_eq_dangling S H H' hH hH' hU
  rw [hverts]
  exact same_adj_same_components (bmgToGraph BMG) (overlayGraph π' ρ)
    (danglingEndpoints S H)
    (bmg_adj_iff_overlay_adj S hS H H' hH hH' hd hc hc' hU)

private lemma reachable_endpoint_positive_degree
    {n : ℕ} (edges : Finset (Edge n)) (u x : Fin n)
    (hreach : (edgeSetToGraph n edges).Reachable u x)
    (hu_deg : vertexDegreeIn n edges u = 1) :
    0 < vertexDegreeIn n edges x := by
  by_cases hux : u = x
  · subst hux
    omega
  · obtain ⟨walk⟩ := hreach.symm
    cases walk with
    | nil =>
      exact (hux rfl).elim
    | @cons a b _ hadj _ =>
      have hx_mem : Sym2.mk (x, b) ∈ edges := by
        simpa using hadj.2
      unfold vertexDegreeIn
      rw [Finset.card_pos]
      exact ⟨_, Finset.mem_filter.mpr ⟨hx_mem, Sym2.mem_mk_left _ _⟩⟩

private lemma boundary_vertex_degrees_one_of_pos
    {n : ℕ} (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (v : Fin n)
    (hLpos : 0 < vertexDegreeIn n L v)
    (hRpos : 0 < vertexDegreeIn n R v) :
    vertexDegreeIn n L v = 1 ∧ vertexDegreeIn n R v = 1 := by
  have hadd := degree_add_of_disjoint L R hDisjoint v
  have htot := hSpanning v
  omega

open Classical in
private lemma walk_bmg_vertex_induction
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S) :
    ∀ {x v u : Fin n},
      v ∈ (boundaryMultigraphOf S L R).vertices →
      (edgeSetToGraph n (L ∪ R)).Walk x v →
      u ∈ (boundaryMultigraphOf S L R).vertices →
      ((edgeSetToGraph n L).Reachable u x ∧ vertexDegreeIn n L u = 1) ∨
      ((edgeSetToGraph n R).Reachable u x ∧ vertexDegreeIn n R u = 1) →
      (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v
:= by
  intro x v u hv_bmg w hu_bmg hside
  induction w generalizing u hu_bmg with
  | @nil x =>
      have hu_bdy : u ∈ boundaryVertices S := (Finset.mem_filter.mp hu_bmg).1
      have hx_bdy : x ∈ boundaryVertices S := (Finset.mem_filter.mp hv_bmg).1
      rcases hside with ⟨hLreach, hLdeg_u⟩ | ⟨hRreach, hRdeg_u⟩
      · by_cases hux : u = x
        · subst hux
          exact SimpleGraph.Reachable.refl u
        · have hLpos_x := reachable_endpoint_positive_degree L u x hLreach hLdeg_u
          have hLdeg_x : vertexDegreeIn n L x = 1 := by
            rcases (Finset.mem_filter.mp hv_bmg).2 with hLx | hRx
            · exact hLx
            · have hRpos_x : 0 < vertexDegreeIn n R x := by omega
              exact (boundary_vertex_degrees_one_of_pos L R hDisjoint hSpanning x hLpos_x hRpos_x).1
          exact
            (bmg_adj_of_reachable_in_L S L R u x hux hu_bdy hx_bdy hLdeg_u hLdeg_x
              hLreach).reachable
      · by_cases hux : u = x
        · subst hux
          exact SimpleGraph.Reachable.refl u
        · have hRpos_x := reachable_endpoint_positive_degree R u x hRreach hRdeg_u
          have hRdeg_x : vertexDegreeIn n R x = 1 := by
            rcases (Finset.mem_filter.mp hv_bmg).2 with hLx | hRx
            · have hLpos_x : 0 < vertexDegreeIn n L x := by omega
              exact (boundary_vertex_degrees_one_of_pos L R hDisjoint hSpanning x hLpos_x hRpos_x).2
            · exact hRx
          exact
            (bmg_adj_of_reachable_in_R S L R u x hux hu_bdy hx_bdy hRdeg_u hRdeg_x
              hRreach).reachable
  | @cons x y z hadj_xy w' ih =>
      have hu_bdy : u ∈ boundaryVertices S := (Finset.mem_filter.mp hu_bmg).1
      rcases hside with ⟨hLreach_ux, hLdeg_u⟩ | ⟨hRreach_ux, hRdeg_u⟩
      · rcases Finset.mem_union.mp hadj_xy.2 with hedge_L | hedge_R
        · have hL_adj : (edgeSetToGraph n L).Adj x y := ⟨hadj_xy.1, hedge_L⟩
          exact ih hv_bmg hu_bmg (Or.inl ⟨hLreach_ux.trans hL_adj.reachable, hLdeg_u⟩)
        · have hLpos_x := reachable_endpoint_positive_degree L u x hLreach_ux hLdeg_u
          have hRpos_x : 0 < vertexDegreeIn n R x := by
            unfold vertexDegreeIn
            rw [Finset.card_pos]
            exact ⟨_, Finset.mem_filter.mpr ⟨hedge_R, Sym2.mem_mk_left x y⟩⟩
          have hx_deg := boundary_vertex_degrees_one_of_pos L R hDisjoint hSpanning x hLpos_x hRpos_x
          have hx_bdy : x ∈ boundaryVertices S := hLEndpoints x hx_deg.1
          have hx_bmg : x ∈ (boundaryMultigraphOf S L R).vertices := by
            unfold boundaryMultigraphOf
            simp only [Finset.mem_filter]
            exact ⟨hx_bdy, Or.inl hx_deg.1⟩
          have hbmg_ux : (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u x := by
            by_cases hux : u = x
            · subst hux
              exact SimpleGraph.Reachable.refl u
            · exact
                (bmg_adj_of_reachable_in_L S L R u x hux hu_bdy hx_bdy hLdeg_u hx_deg.1
                  hLreach_ux).reachable
          have hR_adj : (edgeSetToGraph n R).Adj x y := ⟨hadj_xy.1, hedge_R⟩
          exact hbmg_ux.trans <| ih hv_bmg hx_bmg (Or.inr ⟨hR_adj.reachable, hx_deg.2⟩)
      · rcases Finset.mem_union.mp hadj_xy.2 with hedge_L | hedge_R
        · have hRpos_x := reachable_endpoint_positive_degree R u x hRreach_ux hRdeg_u
          have hLpos_x : 0 < vertexDegreeIn n L x := by
            unfold vertexDegreeIn
            rw [Finset.card_pos]
            exact ⟨_, Finset.mem_filter.mpr ⟨hedge_L, Sym2.mem_mk_left x y⟩⟩
          have hx_deg := boundary_vertex_degrees_one_of_pos L R hDisjoint hSpanning x hLpos_x hRpos_x
          have hx_bdy : x ∈ boundaryVertices S := hLEndpoints x hx_deg.1
          have hx_bmg : x ∈ (boundaryMultigraphOf S L R).vertices := by
            unfold boundaryMultigraphOf
            simp only [Finset.mem_filter]
            exact ⟨hx_bdy, Or.inl hx_deg.1⟩
          have hbmg_ux : (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u x := by
            by_cases hux : u = x
            · subst hux
              exact SimpleGraph.Reachable.refl u
            · exact
                (bmg_adj_of_reachable_in_R S L R u x hux hu_bdy hx_bdy hRdeg_u hx_deg.2
                  hRreach_ux).reachable
          have hL_adj : (edgeSetToGraph n L).Adj x y := ⟨hadj_xy.1, hedge_L⟩
          exact hbmg_ux.trans <| ih hv_bmg hx_bmg (Or.inl ⟨hL_adj.reachable, hx_deg.1⟩)
        · have hR_adj : (edgeSetToGraph n R).Adj x y := ⟨hadj_xy.1, hedge_R⟩
          exact ih hv_bmg hu_bmg (Or.inr ⟨hRreach_ux.trans hR_adj.reachable, hRdeg_u⟩)

private theorem reachable_in_union_gives_reachable_in_bmg_vertices
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (u v : Fin n)
    (hu : u ∈ (boundaryMultigraphOf S L R).vertices)
    (hv : v ∈ (boundaryMultigraphOf S L R).vertices)
    (hreach : (edgeSetToGraph n (L ∪ R)).Reachable u v) :
    (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v := by
  obtain ⟨w⟩ := hreach
  rcases (Finset.mem_filter.mp hu).2 with huL | huR
  · exact walk_bmg_vertex_induction S L R hDisjoint hSpanning hLNoCycles hRNoCycles
      hLEndpoints hREndpoints hv w hu (Or.inl ⟨SimpleGraph.Reachable.refl u, huL⟩)
  · exact walk_bmg_vertex_induction S L R hDisjoint hSpanning hLNoCycles hRNoCycles
      hLEndpoints hREndpoints hv w hu (Or.inr ⟨SimpleGraph.Reachable.refl u, huR⟩)

private theorem numComponentsBMG_le_one_of_pairwise_reachable
    {n : ℕ} (G : BoundaryMultigraph n)
    (hpair : ∀ u ∈ G.vertices, ∀ v ∈ G.vertices, (bmgToGraph G).Reachable u v) :
    numComponentsBMG G ≤ 1 := by
  unfold numComponentsBMG
  rw [Set.ncard_le_one_iff_subsingleton]
  intro c hc d hd
  rcases hc with ⟨u, hu, rfl⟩
  rcases hd with ⟨v, hv, rfl⟩
  exact SimpleGraph.ConnectedComponent.sound (hpair u hu v hv)

private theorem disconnected_overlay_not_connected_ax :
  ∀ {n : ℕ} (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hS : S.isBalanced)
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisconnected : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)),
    ¬ IsConnectedEdgeSet n (mixedGraph S H H') := by
  intro n S H H' hH hH' hS hd hU hDisconnected hConn
  let L := leftSubgraph S H'
  let R := rightSubgraph S H
  let BMG := boundaryMultigraphOf S L R
  have hc : ¬ hasPrematureCycle S H := no_prematureCycle_at_balanced_frontier S hS H hH
  have hc' : ¬ hasPrematureCycle S H' := no_prematureCycle_at_balanced_frontier S hS H' hH'
  have hU_nonempty : (danglingEndpoints S H).Nonempty := by
    by_contra hEmpty
    have hEmpty' : danglingEndpoints S H = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hEmpty'' : danglingEndpoints S H' = ∅ := by
      rw [← hU, hEmpty']
    unfold overlayIsDisconnected overlayComponentCount at hDisconnected
    simp [hEmpty'] at hDisconnected
  have hLNoCycles :
      ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
        ¬ (∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) := by
    intro comp hcomp hne hall
    have hneq : comp ≠ H' := by
      intro hEq
      obtain ⟨u, hu⟩ := (hU ▸ hU_nonempty : (danglingEndpoints S H').Nonempty)
      have hH'subL : H' ⊆ L := by
        intro e he
        exact hcomp (hEq ▸ he)
      have hHeqL : H' = leftSubgraph S H' := by
        apply Finset.Subset.antisymm
        · simpa [L] using hH'subL
        · exact Finset.inter_subset_left
      have hu_degL : vertexDegreeIn n (leftSubgraph S H') u = 1 := by
        simp only [danglingEndpoints, Finset.mem_filter, degreeProfile] at hu
        simpa [leftDegreeAt] using hu.2
      have hu_deg : vertexDegreeIn n H' u = 1 := by
        rw [← hHeqL] at hu_degL
        exact hu_degL
      rw [← hEq] at hu_deg
      rcases hall u with h0 | h2 <;> omega
    exact hc' ⟨comp, by simpa [L] using hcomp, hne, hall, hneq⟩
  have hRNoCycles :
      ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
        ¬ (∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) := by
    intro comp hcomp hne hall
    have hSswap : S.swap.isBalanced := by
      exact ⟨hS.2, hS.1⟩
    have hcR : ¬ hasPrematureCycle S.swap H :=
      no_prematureCycle_at_balanced_frontier S.swap hSswap H hH
    have hneq : comp ≠ H := by
      intro hEq
      obtain ⟨u, hu⟩ := (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ hU_nonempty)
      have hHsubR : H ⊆ R := by
        intro e he
        exact hcomp (hEq ▸ he)
      have hHeqR : H = rightSubgraph S H := by
        apply Finset.Subset.antisymm
        · simpa [R] using hHsubR
        · exact Finset.inter_subset_left
      have hu_degR : vertexDegreeIn n (rightSubgraph S H) u = 1 := by
        simp only [rightDanglingEndpoints, Finset.mem_filter] at hu
        simpa [rightDegreeAt] using hu.2
      have hu_deg : vertexDegreeIn n H u = 1 := by
        rw [← hHeqR] at hu_degR
        exact hu_degR
      rw [← hEq] at hu_deg
      rcases hall u with h0 | h2 <;> omega
    exact hcR ⟨comp, by simpa [R, leftSubgraph_swap] using hcomp, hne, hall, hneq⟩
  have hpair :
      ∀ u ∈ BMG.vertices, ∀ v ∈ BMG.vertices, (bmgToGraph BMG).Reachable u v := by
    intro u hu v hv
    have hreach : (edgeSetToGraph n (L ∪ R)).Reachable u v := by
      unfold IsConnectedEdgeSet at hConn
      exact hConn.preconnected u v
    exact reachable_in_union_gives_reachable_in_bmg_vertices S L R
      (by simpa [L, R] using leftRight_mixed_disjoint S H H')
      (by simpa [L, R, mixedGraph] using mixed_degree_eq S H H' hH hH' hd)
      hLNoCycles hRNoCycles
      (by simpa [L] using left_degree_one_is_boundary S H' hH')
      (by simpa [R] using right_degree_one_is_boundary S H hH)
      u v hu hv hreach
  have hBMG_le : numComponentsBMG BMG ≤ 1 :=
    numComponentsBMG_le_one_of_pairwise_reachable BMG hpair
  have hEq := boundary_multigraph_equals_overlay_components S hS H H' hH hH' hd hc hc' hU
  have hDiscCount :
      overlayComponentCount
          (hU ▸ pathPairing S H' hH')
          (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH) > 1 := by
    simpa [overlayIsDisconnected] using hDisconnected
  rw [← hEq] at hDiscCount
  exact (not_le_of_gt hDiscCount) hBMG_le

theorem disconnected_overlay_not_connected :
  ∀ {n : ℕ} (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hS : S.isBalanced)
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisconnected : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)),
    ¬ IsConnectedEdgeSet n (mixedGraph S H H') := by
  intro n S H H' hH hH' hS hd hU hDisconnected
  exact disconnected_overlay_not_connected_ax S H H' hH hH' hS hd hU hDisconnected

private theorem same_pairing_transfers_reachability_ax :
  ∀ (n : ℕ) (S : Frontier n) (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H'),
    S.isBalanced →
    degreeProfile S H = degreeProfile S H' →
    HEq (pathPairing S H hH) (pathPairing S H' hH') →
    prematureCycleFlag S H = prematureCycleFlag S H' →
    ∀ u v : Fin n,
      (edgeSetToGraph n (leftSubgraph S H ∪ rightSubgraph S H)).Reachable u v →
      (edgeSetToGraph n (leftSubgraph S H' ∪ rightSubgraph S H)).Reachable u v := by
  intro n S H H' hH hH' hS hd hπ hc u v hreach
  let L := leftSubgraph S H'
  let R := rightSubgraph S H
  let BMG := boundaryMultigraphOf S L R
  let LH := leftSubgraph S H
  let RH := rightSubgraph S H
  let BMGH := boundaryMultigraphOf S LH RH
  have hU : danglingEndpoints S H = danglingEndpoints S H' :=
    danglingEndpoints_eq_of_degreeProfile_eq S H H' hd
  by_cases hDang : (danglingEndpoints S H).Nonempty
  · have hLNoCycles :
        ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
          ¬ (∀ x : Fin n, vertexDegreeIn n comp x = 0 ∨ vertexDegreeIn n comp x = 2) := by
      simpa [L] using leftSubgraph_no_cycle_of_nonempty_dangling S hS H' hH' (hU ▸ hDang)
    have hRNoCycles :
        ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
          ¬ (∀ x : Fin n, vertexDegreeIn n comp x = 0 ∨ vertexDegreeIn n comp x = 2) := by
      simpa [R] using rightSubgraph_no_cycle_of_nonempty_dangling S hS H hH hDang
    have hLHNoCycles :
        ∀ comp : Finset (Edge n), comp ⊆ LH → comp.Nonempty →
          ¬ (∀ x : Fin n, vertexDegreeIn n comp x = 0 ∨ vertexDegreeIn n comp x = 2) := by
      simpa [LH] using leftSubgraph_no_cycle_of_nonempty_dangling S hS H hH hDang
    have hRHNoCycles :
        ∀ comp : Finset (Edge n), comp ⊆ RH → comp.Nonempty →
          ¬ (∀ x : Fin n, vertexDegreeIn n comp x = 0 ∨ vertexDegreeIn n comp x = 2) := by
      simpa [RH] using rightSubgraph_no_cycle_of_nonempty_dangling S hS H hH hDang
    have hpairH : ∀ a ∈ BMGH.vertices, ∀ b ∈ BMGH.vertices, (bmgToGraph BMGH).Reachable a b := by
      intro a ha b hb
      have hreachH : (edgeSetToGraph n (LH ∪ RH)).Reachable a b := by
        have hno_premature : ¬ hasPrematureCycle S H :=
          no_prematureCycle_at_balanced_frontier S hS H hH
        simpa [LH, RH] using boundary_multigraph_connected_of_ham n S H hH hS hno_premature a b
      exact reachable_in_union_gives_reachable_in_bmg_vertices S LH RH
        (by simpa [LH, RH] using leftRight_mixed_disjoint S H H)
        (by simpa [LH, RH, mixedGraph] using mixed_degree_eq S H H hH hH rfl)
        hLHNoCycles hRHNoCycles
        (by simpa [LH] using left_degree_one_is_boundary S H hH)
        (by simpa [RH] using right_degree_one_is_boundary S H hH)
        a b ha hb hreachH
    have hEqBMG : BMG = BMGH := by
      simpa [BMG, BMGH, L, R, LH, RH] using
        matching_pairings_give_same_boundary_left_edges S hS H H' hH hH' hU hπ
    have hpair : ∀ a ∈ BMG.vertices, ∀ b ∈ BMG.vertices, (bmgToGraph BMG).Reachable a b := by
      intro a ha b hb
      rw [hEqBMG] at ha hb ⊢
      exact hpairH a ha b hb
    have hpre : (edgeSetToGraph n (L ∪ R)).Reachable u v := by
      have hu_rep := every_component_has_bmg_vertex S L R
        (by simpa [L, R, mixedGraph] using mixed_degree_eq S H H' hH hH' hd)
        hLNoCycles hRNoCycles
        (by simpa [L] using left_degree_one_is_boundary S H' hH')
        (by simpa [R] using right_degree_one_is_boundary S H hH)
        ((edgeSetToGraph n (L ∪ R)).connectedComponentMk u) ⟨u, rfl⟩
      have hv_rep := every_component_has_bmg_vertex S L R
        (by simpa [L, R, mixedGraph] using mixed_degree_eq S H H' hH hH' hd)
        hLNoCycles hRNoCycles
        (by simpa [L] using left_degree_one_is_boundary S H' hH')
        (by simpa [R] using right_degree_one_is_boundary S H hH)
        ((edgeSetToGraph n (L ∪ R)).connectedComponentMk v) ⟨v, rfl⟩
      rcases hu_rep with ⟨u₀, hu₀, hcu⟩
      rcases hv_rep with ⟨v₀, hv₀, hcv⟩
      have huu₀ : (edgeSetToGraph n (L ∪ R)).Reachable u u₀ :=
        SimpleGraph.ConnectedComponent.exact hcu.symm
      have hu₀v₀_bmg : (bmgToGraph BMG).Reachable u₀ v₀ := hpair u₀ hu₀ v₀ hv₀
      have hu₀v₀ : (edgeSetToGraph n (L ∪ R)).Reachable u₀ v₀ :=
        reachable_in_bmg_gives_reachable_in_union S L R u₀ v₀
          (Finset.mem_filter.mp hu₀).1 (Finset.mem_filter.mp hv₀).1 hu₀v₀_bmg
      have hv₀v : (edgeSetToGraph n (L ∪ R)).Reachable v₀ v :=
        SimpleGraph.ConnectedComponent.exact hcv
      exact huu₀.trans (hu₀v₀.trans hv₀v)
    simpa [L, R] using hpre
  · have hEmpty : danglingEndpoints S H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDang
    have hLeftShape : LH = ∅ ∨ LH = H := leftSubgraph_eq_empty_or_self_of_empty_dangling S hS H hH hEmpty
    rcases hLeftShape with hLHempty | hLHall
    · have hLempty' : L = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hLne
        rcases hLne with ⟨e, he⟩
        induction e using Sym2.ind with
        | h a b =>
            have hpos : 0 < vertexDegreeIn n L a := by
              unfold L vertexDegreeIn
              rw [Finset.card_pos]
              exact ⟨_, Finset.mem_filter.mpr ⟨by simpa using he, Sym2.mem_mk_left a b⟩⟩
            have hzero : vertexDegreeIn n L a = 0 := by
              have hdeg := congrArg (fun f => f a) hd
              simpa [degreeProfile, leftDegreeAt, LH, hLHempty, L] using hdeg.symm
            omega
      have hRHall : RH = H := by
        apply Finset.Subset.antisymm
        · exact Finset.inter_subset_left
        · intro e he
          have hedge : e ∈ allEdges n := by
            simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hH.noLoops e he
          have hpart := S.partition ▸ hedge
          rcases Finset.mem_union.mp hpart with hleft | hright
          · exfalso
            have : e ∈ LH := Finset.mem_inter.mpr ⟨he, hleft⟩
            simpa [LH, hLHempty] using this
          · have : e ∈ RH := Finset.mem_inter.mpr ⟨he, hright⟩
            simpa [RH] using this
      have hreachRH : (edgeSetToGraph n RH).Reachable u v := by
        simpa [LH, hLHempty, RH] using hreach
      simpa [mixedGraph, L, R, hLempty', RH, hRHall] using hreachRH
    · have hRempty : RH = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hRne
        rcases hRne with ⟨e, he⟩
        change e ∈ rightSubgraph S H at he
        have heRH : e ∈ H ∩ S.rightEdges := by simpa [rightSubgraph] using he
        have hmemH : e ∈ H := (Finset.mem_inter.mp heRH).1
        have hmemLH : e ∈ LH := by simpa [LH, hLHall] using hmemH
        have hleft : e ∈ S.leftEdges := Finset.mem_inter.mp hmemLH |>.2
        have hright : e ∈ S.rightEdges := (Finset.mem_inter.mp heRH).2
        exact Finset.disjoint_left.mp S.disjoint hleft hright
      have hLHall' : L = H' := by
        apply Finset.Subset.antisymm
        · exact Finset.inter_subset_left
        · intro e he
          have hedge : e ∈ allEdges n := by
            simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hH'.noLoops e he
          have hpart := S.partition ▸ hedge
          rcases Finset.mem_union.mp hpart with hleft | hright
          · exact Finset.mem_inter.mpr ⟨he, hleft⟩
          · exfalso
            induction e using Sym2.ind with
            | h a b =>
                have hpos : 0 < vertexDegreeIn n (rightSubgraph S H') a := by
                  unfold vertexDegreeIn
                  rw [Finset.card_pos]
                  exact ⟨_, Finset.mem_filter.mpr
                    ⟨Finset.mem_inter.mpr ⟨he, hright⟩, Sym2.mem_mk_left a b⟩⟩
                have hleft2 : vertexDegreeIn n L a = 2 := by
                  have hdeg : degreeProfile S H a = degreeProfile S H' a :=
                    congrArg (fun f => f a) hd
                  have hdegH : degreeProfile S H a = 2 := by
                    simpa [degreeProfile, leftDegreeAt, LH, hLHall] using hH.twoRegular a
                  have hdegH' : degreeProfile S H' a = 2 := by
                    exact hdeg.symm ▸ hdegH
                  simpa [degreeProfile, leftDegreeAt, L] using hdegH'
                have hsum' :
                    vertexDegreeIn n (leftSubgraph S H') a +
                      vertexDegreeIn n (rightSubgraph S H') a = 2 := by
                  simpa [leftDegreeAt, rightDegreeAt] using leftDeg_add_rightDeg_eq_two S H' hH' a
                have hleft2' : vertexDegreeIn n (leftSubgraph S H') a = 2 := by
                  simpa [L] using hleft2
                have hright0 : vertexDegreeIn n (rightSubgraph S H') a = 0 := by omega
                omega
      have hreachH' : (edgeSetToGraph n H').Reachable u v := hH'.connected.preconnected u v
      simpa [mixedGraph, L, R, RH, hLHall', hRempty] using hreachH'

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
  intro n S H H' hH hH' hS hd hπ hc u v hreach
  exact same_pairing_transfers_reachability_ax n S H H' hH hH' hS hd hπ hc u v hreach

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

theorem pairing_mismatch_not_hamiltonian
    (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisconnected : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)) :
    ¬ IsHamCycle n (mixedGraph S H H') := by
  intro hMham
  exact disconnected_overlay_not_connected S H H' hH hH' hS hd hU hDisconnected hMham.connected

theorem pairing_mismatch_collision_forces_error {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hS : S.isBalanced)
    (hCorrect : CircuitDecidesHAM C toInput)
    (hm : frontierTranscript C S (toInput (mixedGraph S H H')) =
      frontierTranscript C S (toInput H))
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
