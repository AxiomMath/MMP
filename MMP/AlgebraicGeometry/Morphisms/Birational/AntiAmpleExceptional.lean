/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite

/-!
# An effective Cartier divisor whose negative is relatively ample (Kollár 2.9)

Let `f : X → Y` be a projective, generically finite morphism of normal quasi-projective
varieties. Then there is an effective Cartier divisor `W` on `X` such that `-W` is `f`-ample.

## Main results

* `MMP.Threefold.Resolution.exists_isCartier_isRelativelyAmple_neg_of_isProjectiveMorphism`

## Implementation notes

* As in the source, `W = N f^*D - H`, where `H` is an effective ample Cartier divisor on `X`
  (the divisor of a section of a power of an ample sheaf), `D` is an effective Cartier divisor
  on `Y` with `f(Supp H) ⊆ Supp D` and `f(η_X) ∉ Supp D` (generic finiteness), and `N` is the
  sum of the coefficients of `H`. The pull-back `f^*D` is constructed from the pulled-back local
  equations of `D`, so it is Cartier, and it is principal over the opens of `Y` where `D` is;
  hence `-W = H - N f^*D` is `f`-ample.
* Normality of `Y` is not used; normality of `X` is needed for the Weil divisor framework.
* `f` is *generically finite* if some open `V ⊆ Y` meeting `f(X)` has `f⁻¹(V) → V` finite;
  `Y` is quasi-projective if `s_Y` is H-quasi-projective (an immersion into some `ℙⁿ_k`).

## References

* [J. Kollár, *Lectures on resolution of singularities*, Lemma 2.9][kollar2007]
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Threefold.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Threefold.Resolution

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]

/-- **An effective Cartier divisor `W` with `-W` relatively ample** (Kollár 2.9). Let
`f : X → Y` be a projective, generically finite morphism of `k`-varieties, `X` normal and `Y`
quasi-projective. Then there is an effective Cartier divisor `W` on `X` such that `-W` is
`f`-ample. -/
@[mmp "lem_kr2a_effective_cartier_divisor_negative_relatively_ample"]
theorem exists_isCartier_isRelativelyAmple_neg_of_isProjectiveMorphism [CompactSpace X]
    (hX : Mori.IsVariety k sX)
    (hY : Mori.IsVariety k sY) (hYqp : Stacks.HProjective.IsHQuasiProjective sY)
    {f : X ⟶ Y} (hproj : IsProjectiveMorphism f)
    (hgf : ∃ V : Y.Opens, ((V : Set Y) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V)) :
    ∃ W : Divisor X, 0 ≤ W ∧ ∃ hW : W.IsCartier, (-W).IsRelativelyAmple f hW.neg := by
  classical
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  obtain ⟨-, M, hMinv, hMamp⟩ :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sY hYqp
  have hM : Stacks.Ample.IsAmple Y M :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sY M hMamp
  obtain ⟨L, hLinv, hL⟩ := AlgebraicGeometry.exists_isAmple_of_isQuasiProjective f M hM
    (AlgebraicGeometry.isQuasiProjective_of_isHQuasiProjective f hproj.isHQuasiProjective)
  obtain ⟨IX, hIX, -, hηIX, n, hn, ⟨eX⟩⟩ :=
    exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨H, hH0, hHc, ⟨eH⟩, hHsupp⟩ := exists_divisor_of_isEffectiveCartierDivisor IX hIX
  have := hHc.isInvertibleModule_divisorialSheaf
  have hHf : H.IsRelativelyAmple f hHc := isRelativelyAmple_of_isAmple_divisorialSheaf f hHc
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL))
  have hy₀ : f (genericPoint X) ∉ f.base '' (IX.support : Set X) := by
    rintro ⟨x, hx, hfx⟩
    rw [eq_genericPoint_of_map_eq hgf hfx] at hx
    exact hηIX hx
  obtain ⟨IY, hIY, hTIY, hy₀IY, -⟩ :=
    exists_isEffectiveCartierDivisor_of_isAmple M hM (f.isClosedMap _ IX.support.isClosed) hy₀
  obtain ⟨G, hG0, hGH, hGloc⟩ := exists_divisor_pullback_of_isEffectiveCartierDivisor f IY hIY hy₀IY
  set N : ℤ := ∑ E ∈ H.support, H E
  have hHN : ∀ E, H E ≤ N := by
    intro E
    by_cases hE : E ∈ H.support
    · exact Finset.single_le_sum (fun i _ => hH0 i) hE
    · rw [Finsupp.notMem_support_iff.1 hE]
      exact Finset.sum_nonneg fun i _ => hH0 i
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => hH0 i
  refine ⟨N • G - H, fun E => ?_, ?_⟩
  · change 0 ≤ (N • G - H) E
    rw [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
    have hGE : 0 ≤ G E := hG0 E
    have hHE : 0 ≤ H E := hH0 E
    by_cases hE : 0 < H E
    · nlinarith [hHN E, hGH E (hTIY ⟨E.genericPoint, hHsupp E hE, rfl⟩)]
    · nlinarith [hHN E]
  · have hB := exists_isLocalEquation_neg_zsmul_preimage N hGloc
    have hBc : (-(N • G)).IsCartier := fun x =>
      let ⟨V, hV, ψ, h⟩ := hB (f x)
      ⟨f ⁻¹ᵁ V, hV, ψ, h⟩
    have hrel := isRelativelyAmple_add_of_isLocalEquation_preimage f hHc hHf hBc hB
    have hWc : (N • G - H).IsCartier := by
      have := (hHc.add hBc).neg
      have e : -(H + -(N • G)) = N • G - H := by abel
      rwa [e] at this
    refine ⟨hWc, ?_⟩
    have key : ∀ (D : Divisor X) (hD : D.IsCartier), D = H + -(N • G) →
        D.IsRelativelyAmple f hD := by
      rintro D hD rfl
      exact hrel
    exact key _ _ (by abel)

end MMP.Threefold.Resolution
