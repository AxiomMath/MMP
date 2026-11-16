module

public import MMP.AlgebraicGeometry.Divisor.CoveringTrick.SncDisjointDivisibleCover

/-!
# Making the components of an snc divisor divisible

Let `X` be a smooth projective variety over an algebraically closed field of characteristic zero,
`S` a finite set of prime divisors whose sum is snc, `T ⊆ S` and `m ≥ 2`. There is a finite
surjective `g : Y ⟶ X` from a smooth projective variety with `g^*P = m G_P` for `P ∈ T` and
`g^*P = G_P` for the other `P ∈ S`, the `G_P` reduced, non-zero, of pairwise disjoint supports and
with snc sum. This is the smooth finite cover underlying the covering trick
[KollarMori, 2.67], with `S` kept among the divisors which pull back reduced.

The members of `T` are cleared one at a time, by induction on the number of members of `T`. To
clear `P₀ ∈ T` on a cover where `P₀` pulls back to the reduced divisor `G_{P₀}`, the components of
`G_{P₀}` are pairwise disjoint (`g⁻¹ P₀` is smooth), so
`MMP.FourfoldProofs.FractionalLogComplexProof.exists_cover_clearing_disjoint` clears them together.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_cover_clearing`: the statement above.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.67
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open MMP.Mori
open MMP.Threefold.Resolution (map_componentGenericPoint_notMem_supp_of_isDominant')

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

open Classical in
/-- **The smooth finite cover clearing a set of components.** Let `X` be a smooth projective
variety over an algebraically closed field of characteristic zero, `S` a finite set of prime
divisors with snc sum, `T ⊆ S` and `m ≥ 2`. There is a finite surjective `g : Y ⟶ X` from a smooth
projective variety with `g^*P = m G_P` for `P ∈ T` and `g^*P = G_P` otherwise, the `G_P`
(`P ∈ S`) reduced, non-zero, of pairwise disjoint supports and with snc sum, and two distinct
components of `G_P`, `G_{P'}` (`P, P' ∉ T`) disjoint when `P = P'` or `P ∩ P' = ∅`. -/
theorem exists_cover_clearing (m : ℕ) (hm : 2 ≤ m) {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k f] [Smooth f] [IsLocallyNoetherian X] [IsNormal X]
    (S T : Finset (MMP.Mori.PrimeDivisor X)) (hTS : T ⊆ S)
    (hS : DivisorWithCoeffs.IsSNC f (∑ P ∈ S, Finsupp.single P (1 : ℤ) : Divisor X)) :
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
  obtain ⟨n, hT⟩ : ∃ n, T.card = n := ⟨_, rfl⟩
  induction n generalizing X with
  | zero =>
    rw [Finset.card_eq_zero] at hT
    subst hT
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    refine ⟨X, 𝟙 X, inferInstance, inferInstance,
      by simpa only [Category.id_comp] using ‹MMP.Mori.IsProjectiveVariety k f›,
      by simpa only [Category.id_comp] using ‹Smooth f›,
      inferInstance, inferInstance, inferInstance, fun P => Finsupp.single P 1,
      fun P => map_componentGenericPoint_notMem_supp_of_isDominant' (𝟙 X) _,
      fun P _ => ?_, fun P _ => ?_, fun P _ P' _ h => ?_, fun P _ P' _ _ _ h => ?_, ?_⟩
    · simpa using divisor_isPullback_id (Finsupp.single P (1 : ℤ)) _
    · refine ⟨Finsupp.single_ne_zero.mpr one_ne_zero, fun Q => ?_⟩
      rw [Finsupp.single_apply]
      split_ifs <;> simp
    · rw [Finsupp.support_single _ one_ne_zero,
        Finsupp.support_single _ one_ne_zero]
      exact Finset.disjoint_singleton.mpr h
    · intro Q hQ Q' hQ' hne
      rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hQ hQ'
      subst hQ hQ'
      exact h.resolve_left hne
    · simpa using hS
  | succ n ih =>
    obtain ⟨P₀, hP₀⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    set T' := T.erase P₀ with hT'def
    have hT' : T'.card = n := by rw [Finset.card_erase_of_mem hP₀, hT]; rfl
    have hT'S : T' ⊆ S := (Finset.erase_subset _ _).trans hTS
    have hP₀T' : P₀ ∉ T' := Finset.notMem_erase _ _
    have hP₀S : P₀ ∈ S := hTS hP₀
    -- clear `T'` first
    obtain ⟨Y₁, g₁, _, _, hproj₁, hsm₁, _, _, _, G₁, _, hpb₁, hred₁, hdisj₁, hdisjQ₁, hsnc₁⟩ :=
      ih f S T' hT'S hS hT'
    -- then the components of the pull-back of `P₀`, which are pairwise disjoint
    set S₁ := S.biUnion fun P => (G₁ P).support with hS₁def
    set T₀ := (G₁ P₀).support
    have hmemS₁ : ∀ P ∈ S, ∀ Q ∈ (G₁ P).support, Q ∈ S₁ := fun P hP Q hQ =>
      Finset.mem_biUnion.mpr ⟨P, hP, hQ⟩
    have hS₁ : DivisorWithCoeffs.IsSNC (g₁ ≫ f)
        (∑ Q ∈ S₁, Finsupp.single Q (1 : ℤ) : Divisor Y₁) := by
      rw [← sum_eq_sum_single_one_biUnion S G₁ (fun P hP => (hred₁ P hP).2) hdisj₁]
      exact hsnc₁
    have hT₀S₁ : T₀ ⊆ S₁ := fun Q hQ => hmemS₁ P₀ hP₀S Q hQ
    have hT₀ : T₀.Nonempty := Finsupp.support_nonempty_iff.mpr (hred₁ P₀ hP₀S).1
    have hT₀disj : ∀ Q ∈ T₀, ∀ Q' ∈ T₀, Q ≠ Q' → Disjoint Q.support Q'.support :=
      fun Q hQ Q' hQ' hne => hdisjQ₁ P₀ hP₀S P₀ hP₀S hP₀T' hP₀T' (Or.inl rfl) Q hQ Q' hQ' hne
    have : AlgebraicGeometry.IsProjectiveVariety k (g₁ ≫ f) := hproj₁
    have : Smooth (g₁ ≫ f) := hsm₁
    obtain ⟨Y, g₂, _, _, hproj, hsm, _, _, _, G₂, _, hpb₂, hred₂, hdisj₂, hdisjQ₂, hsnc₂⟩ :=
      exists_cover_clearing_disjoint k (g₁ ≫ f) S₁ T₀ hT₀S₁ hT₀ hS₁ hT₀disj m hm
    have : AlgebraicGeometry.IsProjectiveVariety k (g₂ ≫ g₁ ≫ f) := hproj
    have hcart₁ : ∀ B : Divisor Y₁, B.IsCartier :=
      MMP.Fourfold.isCartier_of_isSmoothScheme ((isSmoothScheme_iff _).2 hsm₁)
    set G : MMP.Mori.PrimeDivisor X → Divisor Y := fun P => ∑ Q ∈ (G₁ P).support, G₂ Q with hGdef
    -- the components over `P ≠ P₀` are not cleared in the second step
    have hT₀iff : ∀ P ∈ S, ∀ Q ∈ (G₁ P).support, (Q ∈ T₀ ↔ P = P₀) := by
      intro P hP Q hQ
      refine ⟨fun h => ?_, fun h => by subst h; exact hQ⟩
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj₁ P hP P₀ hP₀S hne) hQ h
    have hEdisj : ∀ P ∈ S, ∀ Q ∈ (G₁ P).support, ∀ Q' ∈ (G₁ P).support, Q ≠ Q' →
        Disjoint (G₂ Q).support (G₂ Q').support := fun P hP Q hQ Q' hQ' h =>
      hdisj₂ Q (hmemS₁ P hP Q hQ) Q' (hmemS₁ P hP Q' hQ') h
    have hFnonneg : ∀ Q ∈ S₁, 0 ≤ G₂ Q := fun Q hQ R => by
      rcases (hred₂ Q hQ).2 R with h | h <;> simp [h]
    have hmemG : ∀ P ∈ S, ∀ R, R ∈ (G P).support ↔ ∃ Q ∈ (G₁ P).support, R ∈ (G₂ Q).support :=
      fun P hP R => mem_support_sum_iff _ G₂ (fun Q hQ => hFnonneg Q (hmemS₁ P hP Q hQ)) R
    refine ⟨Y, g₂ ≫ g₁, inferInstance, inferInstance, ?_, ?_, inferInstance, inferInstance,
      inferInstance, G, fun P => map_componentGenericPoint_notMem_supp_of_isDominant' (g₂ ≫ g₁) _,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Category.assoc] using hproj
    · simpa only [Category.assoc] using hsm
    · -- the pull-backs
      intro P hP
      set c₁ : ℤ := if P ∈ T' then (m : ℤ) else 1
      have h₁ : Divisor.IsPullback g₁ (Finsupp.single P (1 : ℤ))
          (map_componentGenericPoint_notMem_supp_of_isDominant' g₁ _)
          (c₁ • ∑ Q ∈ (G₁ P).support, Finsupp.single Q (1 : ℤ)) := by
        rw [sum_single_one_support_eq (G₁ P) (hred₁ P hP).2]
        exact hpb₁ P hP
      have h₂ := (divisor_isPullback_sum_single g₂ hcart₁ (G₁ P).support
        (fun Q => (if Q ∈ T₀ then (m : ℤ) else 1) • G₂ Q)
        (fun Q hQ => hpb₂ Q (hmemS₁ P hP Q hQ))).zsmul (hcart₁ _) c₁
        (map_componentGenericPoint_notMem_supp_of_isDominant' g₂ _)
      have e : c₁ • ∑ Q ∈ (G₁ P).support, (if Q ∈ T₀ then (m : ℤ) else 1) • G₂ Q =
          (if P ∈ T then (m : ℤ) else 1) • G P := by
        rw [Finset.sum_congr rfl fun Q hQ => by rw [if_congr (hT₀iff P hP Q hQ) rfl rfl],
          ← Finset.smul_sum, smul_smul]
        congr 1
        by_cases hPP : P = P₀
        · subst hPP
          simp [c₁, hP₀T', hP₀]
        · have hPT : P ∈ T ↔ P ∈ T' := by
            rw [hT'def, Finset.mem_erase]; exact ⟨fun h => ⟨hPP, h⟩, fun h => h.2⟩
          simp [c₁, hPP, hPT]
      rw [e] at h₂
      exact MMP.ProgramBaseChange.divisor_isPullback_comp rfl h₁ h₂ _
    · -- reduced and non-zero
      intro P hP
      refine ⟨fun h0 => ?_, sum_apply_eq_zero_or_eq_one _ G₂
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
      exact Finset.disjoint_left.mp
        (hdisj₂ Q (hmemS₁ P hP Q hQ) Q' (hmemS₁ P' hP' Q' hQ') hQQ) hRQ hRQ'
    · -- disjoint components
      intro P hP P' hP' hPT hP'T hPP R hR R' hR' hRR
      obtain ⟨Q, hQ, hRQ⟩ := (hmemG P hP R).1 hR
      obtain ⟨Q', hQ', hRQ'⟩ := (hmemG P' hP' R').1 hR'
      have hPP₀ : P ≠ P₀ := fun h => hPT (h ▸ hP₀)
      have hP'P₀ : P' ≠ P₀ := fun h => hP'T (h ▸ hP₀)
      have hQT : Q ∉ T₀ := fun h => hPP₀ ((hT₀iff P hP Q hQ).1 h)
      have hQ'T : Q' ∉ T₀ := fun h => hP'P₀ ((hT₀iff P' hP' Q' hQ').1 h)
      have hPT' : P ∉ T' := fun h => hPT (Finset.mem_of_mem_erase h)
      have hP'T' : P' ∉ T' := fun h => hP'T (Finset.mem_of_mem_erase h)
      by_cases hQQ : Q = Q'
      · subst hQQ
        exact hdisjQ₂ Q (hmemS₁ P hP Q hQ) Q (hmemS₁ P' hP' Q hQ') hQT hQ'T (Or.inl rfl) R hRQ
          R' hRQ' hRR
      · exact hdisjQ₂ Q (hmemS₁ P hP Q hQ) Q' (hmemS₁ P' hP' Q' hQ') hQT hQ'T
          (Or.inr (hdisjQ₁ P hP P' hP' hPT' hP'T' hPP Q hQ Q' hQ' hQQ)) R hRQ R' hRQ' hRR
    · -- snc
      have e : ∑ P ∈ S, G P = ∑ Q ∈ S₁, G₂ Q := by
        rw [hGdef, hS₁def, Finset.sum_biUnion (fun P hP P' hP' h => hdisj₁ P hP P' hP' h)]
      rw [e]
      simpa only [Category.assoc] using hsnc₂

end MMP.FourfoldProofs.FractionalLogComplexProof
