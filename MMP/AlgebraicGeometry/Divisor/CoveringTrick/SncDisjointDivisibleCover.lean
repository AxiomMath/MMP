module

public import MMP.AlgebraicGeometry.Vanishing.CoveringTrick
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms

/-!
# Making pairwise disjoint components of an snc divisor divisible

Let `X` be a smooth projective variety over an algebraically closed field of characteristic zero,
`S` a finite set of prime divisors whose sum is snc, `T ⊆ S` a non-empty set of pairwise disjoint
members and `m ≥ 2`. A Bloch–Gieseker cover makes `∑_{P ∈ T} P` linearly equivalent to an `m`-th
multiple, and the cyclic cover of degree `m` branched along its (smooth) pull-back ramifies to
order `m` along it. The composite `g : Y ⟶ X` is finite and surjective from a smooth projective
variety, `g^*P = m G_P` for `P ∈ T` and `g^*P = G_P` for the other `P ∈ S`, with the `G_P` reduced,
non-zero, of pairwise disjoint supports and with snc sum; two distinct components of `G_P`,
`G_{P'}` (`P, P' ∉ T`) are disjoint when `P = P'` or `P ∩ P' = ∅`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_cover_clearing_disjoint`: the statement above.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open MMP.Mori
open MMP.Threefold.Resolution (map_componentGenericPoint_notMem_supp_of_isDominant')

section Sums

universe u

variable {Y : Scheme.{u}}

/-- A reduced effective divisor is the sum of its components. -/
theorem sum_single_one_support_eq (E : Divisor Y) (hE : ∀ Q, E Q = 0 ∨ E Q = 1) :
    (∑ Q ∈ E.support, Finsupp.single Q (1 : ℤ) : Divisor Y) = E := by
  classical
  refine Finsupp.ext fun Q => ?_
  rw [sum_single_one_apply]
  rcases hE Q with h | h
  · simp [Finsupp.notMem_support_iff.mpr h, h]
  · have hQ : Q ∈ E.support := Finsupp.mem_support_iff.mpr (by rw [h]; exact one_ne_zero)
    simp [hQ, h]

/-- A sum of reduced effective divisors with pairwise disjoint supports is the reduced sum of the
union of their components. -/
theorem sum_eq_sum_single_one_biUnion {ι : Type*} [DecidableEq (MMP.Mori.PrimeDivisor Y)]
    (A : Finset ι) (E : ι → Divisor Y) (hE : ∀ i ∈ A, ∀ Q, E i Q = 0 ∨ E i Q = 1)
    (hdisj : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (E i).support (E j).support) :
    ∑ i ∈ A, E i = ∑ Q ∈ A.biUnion (fun i => (E i).support), Finsupp.single Q (1 : ℤ) := by
  rw [Finset.sum_biUnion (fun i hi j hj hij => hdisj i hi j hj hij)]
  exact Finset.sum_congr rfl fun i hi => (sum_single_one_support_eq (E i) (hE i hi)).symm

/-- The components of a sum of effective divisors are those of the summands. -/
theorem mem_support_sum_iff {ι : Type*} (A : Finset ι) (E : ι → Divisor Y)
    (hE : ∀ i ∈ A, 0 ≤ E i) (Q : MMP.Mori.PrimeDivisor Y) :
    Q ∈ (∑ i ∈ A, E i).support ↔ ∃ i ∈ A, Q ∈ (E i).support := by
  simp only [Finsupp.mem_support_iff, Finsupp.coe_finsetSum, Finset.sum_apply, ne_eq]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i hi => hE i hi Q]
  simp only [not_forall, exists_prop]

/-- A sum of reduced effective divisors with pairwise disjoint supports is reduced. -/
theorem sum_apply_eq_zero_or_eq_one {ι : Type*} (A : Finset ι) (E : ι → Divisor Y)
    (hE : ∀ i ∈ A, ∀ Q, E i Q = 0 ∨ E i Q = 1)
    (hdisj : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (E i).support (E j).support)
    (Q : MMP.Mori.PrimeDivisor Y) :
    (∑ i ∈ A, E i) Q = 0 ∨ (∑ i ∈ A, E i) Q = 1 := by
  classical
  rw [Finsupp.coe_finsetSum, Finset.sum_apply]
  by_cases h : ∃ i ∈ A, Q ∈ (E i).support
  · obtain ⟨i, hi, hQ⟩ := h
    rw [Finset.sum_eq_single_of_mem i hi fun j hj hji =>
      Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp (hdisj i hi j hj hji.symm) hQ)]
    exact hE i hi Q
  · simp only [not_exists, not_and] at h
    left
    exact Finset.sum_eq_zero fun i hi => Finsupp.notMem_support_iff.mp (h i hi)

end Sums

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

open Classical in
/-- **Clearing pairwise disjoint components.** Let `X` be a smooth projective variety over an
algebraically closed field of characteristic zero, `S` a finite set of prime divisors with snc
sum, `T ⊆ S` non-empty with pairwise disjoint members, and `m ≥ 2`. There is a finite surjective
`g : Y ⟶ X` from a smooth projective variety with `g^*P = m G_P` for `P ∈ T` and `g^*P = G_P`
otherwise, the `G_P` (`P ∈ S`) reduced, non-zero, of pairwise disjoint supports and with snc sum,
and two distinct components of `G_P`, `G_{P'}` (`P, P' ∉ T`) disjoint when `P = P'` or
`P ∩ P' = ∅`. -/
theorem exists_cover_clearing_disjoint {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k f] [Smooth f] [IsLocallyNoetherian X] [IsNormal X]
    (S T : Finset (MMP.Mori.PrimeDivisor X)) (hTS : T ⊆ S) (hT : T.Nonempty)
    (hS : DivisorWithCoeffs.IsSNC f (∑ P ∈ S, Finsupp.single P (1 : ℤ) : Divisor X))
    (hTdisj : ∀ P ∈ T, ∀ P' ∈ T, P ≠ P' → Disjoint P.support P'.support)
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ (Y : Scheme.{0}) (g : Y ⟶ X) (_ : IsFinite g) (_ : Surjective g)
      (_ : MMP.Mori.IsProjectiveVariety k (g ≫ f)) (_ : Smooth (g ≫ f))
      (_ : IsLocallyNoetherian Y) (_ : IsNormal Y) (_ : CompactSpace Y)
      (G : MMP.Mori.PrimeDivisor X → Divisor Y)
      (hgen : ∀ (P : MMP.Mori.PrimeDivisor X) (C : irreducibleComponents Y),
        g (componentGenericPoint Y C) ∉ DivisorWithCoeffs.supp (Finsupp.single P (1 : ℤ))),
      (∀ P ∈ S, Divisor.IsPullback g (Finsupp.single P (1 : ℤ)) (hgen P)
        ((if P ∈ T then (m : ℤ) else 1) • G P)) ∧
      (∀ P ∈ S, G P ≠ 0 ∧ ∀ Q, G P Q = 0 ∨ G P Q = 1) ∧
      (∀ P ∈ S, ∀ P' ∈ S, P ≠ P' → Disjoint (G P).support (G P').support) ∧
      (∀ P ∈ S, ∀ P' ∈ S, P ∉ T → P' ∉ T → (P = P' ∨ Disjoint P.support P'.support) →
        ∀ Q ∈ (G P).support, ∀ Q' ∈ (G P').support, Q ≠ Q' → Disjoint Q.support Q'.support) ∧
      DivisorWithCoeffs.IsSNC (g ≫ f) (∑ P ∈ S, G P) := by
  -- the Bloch–Gieseker cover
  obtain ⟨Y₁, g₁, _, _, hproj₁, hsm₁, _, _, _, E, D, hgen₁, hpb₁, hred₁, hdisj₁, hdisjQ₁, hsnc₁,
    hlin₁⟩ := exists_bloch_gieseker_cover_divisors k f S T hTS hS m (by omega)
  set S₁ := S.biUnion fun P => (E P).support with hS₁def
  set T₁ := T.biUnion fun P => (E P).support
  have hS₁ : DivisorWithCoeffs.IsSNC (g₁ ≫ f)
      (∑ Q ∈ S₁, Finsupp.single Q (1 : ℤ) : Divisor Y₁) := by
    rw [← sum_eq_sum_single_one_biUnion S E (fun P hP => (hred₁ P hP).2) hdisj₁]
    exact hsnc₁
  have hT₁S₁ : T₁ ⊆ S₁ := Finset.biUnion_subset_biUnion_of_subset_left _ hTS
  have hT₁ : T₁.Nonempty := by
    obtain ⟨P, hP⟩ := hT
    obtain ⟨Q, hQ⟩ := Finsupp.support_nonempty_iff.mpr (hred₁ P (hTS hP)).1
    exact ⟨Q, Finset.mem_biUnion.mpr ⟨P, hP, hQ⟩⟩
  have hT₁disj : ∀ Q ∈ T₁, ∀ Q' ∈ T₁, Q ≠ Q' → Disjoint Q.support Q'.support := by
    intro Q hQ Q' hQ' hne
    obtain ⟨P, hP, hQP⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨P', hP', hQP'⟩ := Finset.mem_biUnion.mp hQ'
    refine hdisjQ₁ P (hTS hP) P' (hTS hP') ?_ Q hQP Q' hQP' hne
    by_cases hPP : P = P'
    · exact Or.inl hPP
    · exact Or.inr (hTdisj P hP P' hP' hPP)
  have hD₁ : Divisor.LinearlyEquivalent (∑ Q ∈ T₁, Finsupp.single Q (1 : ℤ)) ((m : ℤ) • D) := by
    rw [← sum_eq_sum_single_one_biUnion T E (fun P hP => (hred₁ P (hTS hP)).2)
      (fun P hP P' hP' h => hdisj₁ P (hTS hP) P' (hTS hP') h)]
    exact hlin₁
  -- the cyclic cover
  have : AlgebraicGeometry.IsProjectiveVariety k (g₁ ≫ f) := hproj₁
  have : Smooth (g₁ ≫ f) := hsm₁
  obtain ⟨Y, g₂, _, _, hproj, hsm, _, _, _, F, hgen₂, hpb₂, hred₂, hdisj₂, hdisjQ₂, hsnc₂, -⟩ :=
    exists_cyclic_cover_divisors k (g₁ ≫ f) S₁ T₁ hT₁S₁ hT₁ hS₁ hT₁disj m hm D hD₁
  have : AlgebraicGeometry.IsProjectiveVariety k (g₂ ≫ g₁ ≫ f) := hproj
  have : IsIntegral X := (inferInstance : AlgebraicGeometry.IsProjectiveVariety k f).toIsIntegral
  have : IsIntegral Y₁ := hproj₁.toIsIntegral
  have : IsIntegral Y := hproj.toIsIntegral
  have hcart₁ : ∀ B : Divisor Y₁, B.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme ((isSmoothScheme_iff _).2 hsm₁)
  set G : MMP.Mori.PrimeDivisor X → Divisor Y := fun P => ∑ Q ∈ (E P).support, F Q with hGdef
  have hmemS₁ : ∀ P ∈ S, ∀ Q ∈ (E P).support, Q ∈ S₁ := fun P hP Q hQ =>
    Finset.mem_biUnion.mpr ⟨P, hP, hQ⟩
  have hT₁iff : ∀ P ∈ S, ∀ Q ∈ (E P).support, (Q ∈ T₁ ↔ P ∈ T) := by
    intro P hP Q hQ
    refine ⟨fun h => ?_, fun h => Finset.mem_biUnion.mpr ⟨P, h, hQ⟩⟩
    obtain ⟨P', hP', hQ'⟩ := Finset.mem_biUnion.mp h
    by_contra hPT
    have hne : P ≠ P' := fun he => hPT (he ▸ hP')
    exact Finset.disjoint_left.mp (hdisj₁ P hP P' (hTS hP') hne) hQ hQ'
  have hEdisj : ∀ P ∈ S, ∀ Q ∈ (E P).support, ∀ Q' ∈ (E P).support, Q ≠ Q' →
      Disjoint (F Q).support (F Q').support := fun P hP Q hQ Q' hQ' h =>
    hdisj₂ Q (hmemS₁ P hP Q hQ) Q' (hmemS₁ P hP Q' hQ') h
  have hFnonneg : ∀ Q ∈ S₁, 0 ≤ F Q := fun Q hQ R => by
    rcases (hred₂ Q hQ).2 R with h | h <;> simp [h]
  have hmemG : ∀ P ∈ S, ∀ R, R ∈ (G P).support ↔ ∃ Q ∈ (E P).support, R ∈ (F Q).support :=
    fun P hP R => mem_support_sum_iff _ F (fun Q hQ => hFnonneg Q (hmemS₁ P hP Q hQ)) R
  refine ⟨Y, g₂ ≫ g₁, inferInstance, inferInstance, ?_, ?_, inferInstance, inferInstance,
    inferInstance, G, fun P => map_componentGenericPoint_notMem_supp_of_isDominant' (g₂ ≫ g₁) _,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Category.assoc] using hproj
  · simpa only [Category.assoc] using hsm
  · -- the pull-backs
    intro P hP
    have h₁ : Divisor.IsPullback g₁ (Finsupp.single P (1 : ℤ))
        (map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _)
        (∑ Q ∈ (E P).support, Finsupp.single Q (1 : ℤ)) := by
      rw [sum_single_one_support_eq (E P) (hred₁ P hP).2]
      exact hpb₁ P hP
    have h₂ := divisor_isPullback_sum_single g₂ hcart₁ (E P).support
      (fun Q => (if Q ∈ T₁ then (m : ℤ) else 1) • F Q)
      (fun Q hQ => hpb₂ Q (hmemS₁ P hP Q hQ))
    have e : ∑ Q ∈ (E P).support, (if Q ∈ T₁ then (m : ℤ) else 1) • F Q =
        (if P ∈ T then (m : ℤ) else 1) • G P := by
      rw [hGdef, Finset.smul_sum]
      exact Finset.sum_congr rfl fun Q hQ => by rw [if_congr (hT₁iff P hP Q hQ) rfl rfl]
    rw [e] at h₂
    exact MMP.ProgramBaseChange.divisor_isPullback_comp rfl h₁ h₂ _
  · -- reduced and non-zero
    intro P hP
    refine ⟨fun h0 => ?_, sum_apply_eq_zero_or_eq_one _ F
      (fun Q hQ => (hred₂ Q (hmemS₁ P hP Q hQ)).2) (hEdisj P hP)⟩
    obtain ⟨Q, hQ⟩ := Finsupp.support_nonempty_iff.mpr (hred₁ P hP).1
    obtain ⟨R, hR⟩ := Finsupp.support_nonempty_iff.mpr (hred₂ Q (hmemS₁ P hP Q hQ)).1
    have := (hmemG P hP R).2 ⟨Q, hQ, hR⟩
    rw [h0] at this
    simp at this
  · -- disjoint supports
    intro P hP P' hP' hne
    refine Finset.disjoint_left.mpr fun R hR hR' => ?_
    obtain ⟨Q, hQ, hRQ⟩ := (hmemG P hP R).1 hR
    obtain ⟨Q', hQ', hRQ'⟩ := (hmemG P' hP' R).1 hR'
    have hQQ : Q ≠ Q' := fun he =>
      Finset.disjoint_left.mp (hdisj₁ P hP P' hP' hne) hQ (he ▸ hQ')
    exact Finset.disjoint_left.mp (hdisj₂ Q (hmemS₁ P hP Q hQ) Q' (hmemS₁ P' hP' Q' hQ') hQQ)
      hRQ hRQ'
  · -- disjoint components
    intro P hP P' hP' hPT hP'T hPP R hR R' hR' hRR
    obtain ⟨Q, hQ, hRQ⟩ := (hmemG P hP R).1 hR
    obtain ⟨Q', hQ', hRQ'⟩ := (hmemG P' hP' R').1 hR'
    have hQT : Q ∉ T₁ := fun h => hPT ((hT₁iff P hP Q hQ).1 h)
    have hQ'T : Q' ∉ T₁ := fun h => hP'T ((hT₁iff P' hP' Q' hQ').1 h)
    by_cases hQQ : Q = Q'
    · subst hQQ
      exact hdisjQ₂ Q (hmemS₁ P hP Q hQ) Q (hmemS₁ P' hP' Q hQ') hQT hQ'T (Or.inl rfl) R hRQ R'
        hRQ' hRR
    · exact hdisjQ₂ Q (hmemS₁ P hP Q hQ) Q' (hmemS₁ P' hP' Q' hQ') hQT hQ'T
        (Or.inr (hdisjQ₁ P hP P' hP' hPP Q hQ Q' hQ' hQQ)) R hRQ R' hRQ' hRR
  · -- snc
    have e : ∑ P ∈ S, G P = ∑ Q ∈ S₁, F Q := by
      rw [hGdef, hS₁def, Finset.sum_biUnion (fun P hP P' hP' h => hdisj₁ P hP P' hP' h)]
    rw [e]
    simpa only [Category.assoc] using hsnc₂

end MMP.FourfoldProofs.FractionalLogComplexProof
