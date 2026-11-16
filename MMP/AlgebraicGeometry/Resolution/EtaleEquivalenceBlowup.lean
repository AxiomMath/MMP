module

public import MMP.AlgebraicGeometry.Resolution.MaximalContact.AlongBlowupSequence
import MMP.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Kollár's resolution: étale equivalence and the logarithmic decomposition

Three steps of the uniqueness and blow-up analysis in Kollár's proof of resolution of
singularities, over a field `k` of characteristic zero, for a smooth equidimensional `k`-scheme
`X` of finite type whose irreducible components have positive dimension.

**The étale equivalence lifts through a blow-up** (proof of Theorem 3.97). Let `I` be an ideal
sheaf nonzero on every component with `m = maxord I ≥ 1`, and let `𝐁 = (X_l, Z_l)`,
`𝐁' = (X'_l, Z'_l)` be smooth blow-up sequences of order `m` starting with `(X, I)`, étale
equivalent via `ψ, ψ' : U → X`, with projections `ψ_l : U_l → X_l`, `ψ'_l : U_l → X'_l`. Put
`M_l = T_l(D^{m-1}(ψ^*I), 1)` along `ψ^*𝐁`. If `Z_l = Z'_l` for `l ≤ i` and
`(ψ_i, ψ'_i)^*I_{Δ_{X_i}} ⊆ M_i`, then `(ψ_{i+1}, ψ'_{i+1})^*I_{Δ_{X_{i+1}}} ⊆ M_{i+1}`, where
`I_{Δ_Y}` is the ideal of the diagonal of `Y ×_k Y`. The inclusion `(f, g)^*I_Δ ⊆ J` says that
`f` and `g` agree on `V(J)`; on the charts `D_+(a)` of the blow-up this is a computation with
the non-zero-divisor `a`.

**Étale realization of the formal equivalence** (3.95). Given two hypersurfaces `H, H'` of
maximal contact for `I` at a closed point `p`, with local coordinates `(x₁, y)` and `(x₁', y)` on
an affine `V ∋ p`, the fibre product `W = V ×_{a, 𝔸ⁿ_k, a'} V` of the two coordinate maps carries
an open `U` around a closed point over `p` on which the projections `ψ, ψ'` are étale and
satisfy `ψ⁻¹H = ψ'⁻¹H'`, `ψ^*I = ψ'^*I`, `ψ⁻¹E^i = ψ'⁻¹E^i` and
`(ψ, ψ')^*I_Δ ⊆ D^{m-1}(ψ^*I)`. These hold in the completion at `w` by the formal uniqueness of
hypersurfaces of maximal contact, and spread out to a neighbourhood.

**Logarithmic decomposition for one blow-up** (3.88.2). For a smooth hypersurface `S`, a smooth
`Z ⊆ S` with blow-up `π : B_Z X → X`, exceptional divisor `F` and `S₁ = B_Z S`, and `I` with
`ord_Z I ≥ m`, for `s ≤ m`:
`D^s(𝒪(mF)·π^*I) = ∑_{j ≤ s} D^{s-j}(-log S₁)(𝒪((m-j)F)·π^*D^j I)`.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.ker_diagonal_comap_le_derivedTransform_succ`
* `MMP.Resolution.exists_etale_realization_of_formalUniqueness`
* `MMP.Resolution.higherDerivativeIdeal_birationalTransform_eq_iSup`

## Implementation notes

In `ker_diagonal_comap_le_derivedTransform_succ`, since `𝐁` and `𝐁'` agree up to step `i + 1`,
the projections `ψ'_l` are those of the pull-back of the truncation `𝐁_{≤ l}` along `ψ'`, their
source identified with that of `ψ_l` through `MMP.Resolution.Kollar.pullback_truncate`. The
transforms `T_l` are `Option`-valued (`derivedTransform`); the conclusion asserts that `M_{i+1}`
is an ideal sheaf containing the pulled-back diagonal ideal.

In `exists_etale_realization_of_formalUniqueness` the coordinates `x₂, …, xₙ` are indexed by
`Fin n`, the coordinate maps are `AlgebraicGeometry.AffineSpace.homOfVector` with index type
`ULift (Fin (n + 1))`, and the conditions are stated for the restrictions `U.ι ≫ ψ`,
`U.ι ≫ ψ'`. No separatedness of `X` is needed, since `ψ` and `ψ'` factor through the affine `V`.

In `higherDerivativeIdeal_birationalTransform_eq_iSup` the ideal `𝒪((m-j)F)·π^*D^j I` is that of
`MarkedIdeal.birationalTransform Z ⟨D^j I, m - j⟩`, `S₁` is the kernel of the canonical lift
`B_Z S → B_Z X`, and the sum of ideal sheaves is their supremum.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 3.88.2, 3.95, 3.97
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Étale equivalence lifts through a blow-up -/

section EtaleEquivalence

open ClosedBlowupSequence

private theorem length_pullback {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X) :
    (B.pullback h).length = B.length := by
  induction B generalizing Y with
  | nil X => rfl
  | cons Z B ih =>
    simp only [ClosedBlowupSequence.pullback, ClosedBlowupSequence.length, ih]

/-- The base of a smooth blow-up sequence of order `m` is smooth. -/
private theorem isSmoothScheme_of_isOrderMPlainSeq {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {m : ℕ} {B : ClosedBlowupSequence X}
    (h : B.IsOrderMPlainSeq s I m) : MMP.Mori.IsSmoothScheme s := by
  cases B with
  | nil => exact h.1
  | cons => exact h.1

/-- A nonempty scheme of relative dimension `d` over a field is equidimensional of
dimension `d`. -/
private theorem equidimensional_of_relativeDimension {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [Nonempty X] {d : ℕ}
    (h : RelativeDimension f d) : Equidimensional X ∧ topologicalKrullDim X = d := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨x⟩ := ‹Nonempty X›
  have hpre : f.base ⁻¹' {f.base x} = (Set.univ : Set X) := by
    ext y
    simp [Subsingleton.elim (f.base y) (f.base x)]
  let e : f.fiber (f.base x) ≃ₜ X :=
    (f.fiberHomeo _).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ X))
  obtain ⟨h1, h2⟩ := h (f.base x) ⟨e.symm x⟩
  exact ⟨Equidimensional.of_homeomorph e.symm h1,
    (IsHomeomorph.topologicalKrullDim_eq e.symm e.symm.isHomeomorph).trans h2⟩

/-- On an equidimensional space every irreducible component has the dimension of the space. -/
private theorem topologicalKrullDim_eq_of_mem_irreducibleComponents {T : Type*}
    [TopologicalSpace T] (h : Equidimensional T) {C : Set T} (hC : C ∈ irreducibleComponents T) :
    topologicalKrullDim C = topologicalKrullDim T := by
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents T]
  refine le_antisymm (le_iSup₂ (f := fun W (_ : W ∈ irreducibleComponents T) =>
    topologicalKrullDim W) C hC) ?_
  exact iSup₂_le fun W hW => (h W hW C hC).le

/-- A scheme étale over an equidimensional scheme of finite type over a field, whose
irreducible components have positive dimension, is equidimensional with irreducible components
of positive dimension. -/
private theorem equidimensional_of_etale {k : Type u} [Field k] {X U : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : Equidimensional X) (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (ψ : U ⟶ X) [Etale ψ] :
    Equidimensional U ∧ ∀ Z ∈ irreducibleComponents U, 0 < topologicalKrullDim Z := by
  rcases isEmpty_or_nonempty U with hU | hU
  · have hnil : ∀ Z ∈ irreducibleComponents U, False := fun Z hZ => by
      obtain ⟨z, -⟩ := hZ.1.nonempty
      exact isEmptyElim z
    exact ⟨fun Z hZ => (hnil Z hZ).elim, fun Z hZ => (hnil Z hZ).elim⟩
  have : Nonempty X := ⟨ψ hU.some⟩
  have : CompactSpace X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have h0 := hdim _ (irreducibleComponent_mem_irreducibleComponents x)
  rw [topologicalKrullDim_eq_of_mem_irreducibleComponents hX
    (irreducibleComponent_mem_irreducibleComponents x)] at h0
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim X = d := by
    have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
    have h2 : topologicalKrullDim X ≠ ⊥ := ne_bot_of_gt h0
    obtain ⟨t, ht⟩ := WithBot.ne_bot_iff_exists.mp h2
    obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp (show t ≠ ⊤ by rintro rfl; exact h1 ht.symm)
    exact ⟨d, ht.symm⟩
  have hX' := relativeDimension_of_equidimensional k sX hX d hd
  have hψ0 : RelativeDimension ψ 0 :=
    (locallyQuasiFinite_iff_relativeDimension_zero ψ).mp (locallyQuasiFinite_of_etale ψ).2
  have hU' := hψ0.comp_of_flat ψ sX hX'
  rw [zero_add] at hU'
  obtain ⟨hUe, hUd⟩ := equidimensional_of_relativeDimension (ψ ≫ sX) hU'
  refine ⟨hUe, fun Z hZ => ?_⟩
  rw [topologicalKrullDim_eq_of_mem_irreducibleComponents hUe hZ, hUd, ← hd]
  exact h0

/-- If two morphisms agree on the closed subscheme `J`, the pulled-back diagonal ideal is
contained in `J`. -/
private theorem ker_diagonal_comap_le_of_eq {T W S : Scheme.{u}} {s : W ⟶ S} (f g : T ⟶ W)
    (h : f ≫ s = g ≫ s) (J : T.IdealSheafData) (hJ : J.subschemeι ≫ f = J.subschemeι ≫ g) :
    (pullback.diagonal s).ker.comap (pullback.lift f g h) ≤ J := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map]
  have : J.subschemeι ≫ pullback.lift f g h = (J.subschemeι ≫ f) ≫ pullback.diagonal s := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hJ]
  rw [this]
  exact Scheme.Hom.le_ker_comp _ _

/-- Conversely, over a separated base, the pulled-back diagonal ideal contained in `J` makes the
morphisms agree on `J`. -/
private theorem eq_of_ker_diagonal_comap_le {T W S : Scheme.{u}} {s : W ⟶ S} [IsSeparated s]
    (f g : T ⟶ W) (h : f ≫ s = g ≫ s) (J : T.IdealSheafData)
    (hJ : (pullback.diagonal s).ker.comap (pullback.lift f g h) ≤ J) :
    J.subschemeι ≫ f = J.subschemeι ≫ g := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map] at hJ
  have hl := IsClosedImmersion.lift_fac (pullback.diagonal s) (J.subschemeι ≫ pullback.lift f g h)
    hJ
  have h1 := congrArg (· ≫ pullback.fst s s) hl
  have h2 := congrArg (· ≫ pullback.snd s s) hl
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at h1 h2
  rw [← h1, ← h2]

/-- Morphisms agreeing on `J` agree on sections modulo `J`. -/
private theorem appLE_sub_mem_of_eq {T W : Scheme.{u}} (f g : T ⟶ W) (J : T.IdealSheafData)
    (hJ : J.subschemeι ≫ f = J.subschemeι ≫ g) (O : T.affineOpens) (C : W.Opens)
    (hf : O.1 ≤ f ⁻¹ᵁ C) (hg : O.1 ≤ g ⁻¹ᵁ C) (y : Γ(W, C)) :
    f.appLE C O.1 hf y - g.appLE C O.1 hg y ∈ J.ideal O := by
  rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker, map_sub, sub_eq_zero,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (φ ψ : J.subscheme ⟶ W) (_ : φ = ψ) (e e'), φ.appLE C (J.subschemeι ⁻¹ᵁ O.1) e =
      ψ.appLE C (J.subschemeι ⁻¹ᵁ O.1) e' := by
    rintro _ _ rfl _ _; rfl
  rw [key _ _ hJ]

/-- Two morphisms agree on `J` once they agree on sections modulo `J` near every point of `J`. -/
private theorem eq_of_forall_appLE_sub_mem {T W : Scheme.{u}} (f g : T ⟶ W) (J : T.IdealSheafData)
    (H : ∀ v ∈ J.support, ∃ (O : T.affineOpens) (C : W.affineOpens) (hf : O.1 ≤ f ⁻¹ᵁ C.1)
      (hg : O.1 ≤ g ⁻¹ᵁ C.1), v ∈ O.1 ∧
        ∀ y, f.appLE C.1 O.1 hf y - g.appLE C.1 O.1 hg y ∈ J.ideal O) :
    J.subschemeι ≫ f = J.subschemeι ≫ g := by
  refine Scheme.hom_ext_of_forall _ _ fun q => ?_
  have hq : J.subschemeι q ∈ J.support := by
    change J.subschemeι q ∈ (J.support : Set T)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨q, rfl⟩
  obtain ⟨O, C, hf, hg, hv, hy⟩ := H _ hq
  refine ⟨J.subschemeι ⁻¹ᵁ O.1, hv, ?_⟩
  have ef : J.subschemeι ⁻¹ᵁ O.1 ≤ (J.subschemeι ≫ f) ⁻¹ᵁ C.1 := fun x hx => hf hx
  have eg : J.subschemeι ⁻¹ᵁ O.1 ≤ (J.subschemeι ≫ g) ⁻¹ᵁ C.1 := fun x hx => hg hx
  rw [← Scheme.Hom.resLE_comp_ι _ ef,
    ← Scheme.Hom.resLE_comp_ι _ eg]
  congr 1
  have : IsAffine C.1.toScheme := C.2
  apply ext_of_isAffine
  rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top]
  congr 2
  rw [← Scheme.Hom.appLE_comp_appLE J.subschemeι f C.1 O.1 _ hf le_rfl,
    ← Scheme.Hom.appLE_comp_appLE J.subschemeι g C.1 O.1 _ hg le_rfl, Scheme.Hom.appLE_eq_app]
  ext y
  have := hy y
  rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker, map_sub, sub_eq_zero] at this
  simpa only [CommRingCat.comp_apply] using this

/-- **The chart computation.** Let `F, G : C → O` be ring maps extending `PA, PB : R → O`
through `πC : R → C`, let `E = PA(Z) = (PA a)` with `PA a` a non-zero-divisor, `PB(Z) ⊆ E`, and
`PA u - PB u ∈ M_1 E` for every `u`. If `y · πC(a)^n = πC(x)` with `x ∈ Zⁿ`, then
`F y - G y ∈ M_1`. -/
private theorem sub_mem_of_chart {R C O : Type*} [CommRing R] [CommRing C] [CommRing O]
    (πC : R →+* C) (F G : C →+* O) (PA PB : R →+* O) (hF : ∀ u, F (πC u) = PA u)
    (hG : ∀ u, G (πC u) = PB u) (Zr : Ideal R) (M₁ : Ideal O) (a : R)
    (hE : Zr.map PA = Ideal.span {PA a}) (hE' : Zr.map PB ≤ Zr.map PA)
    (ht : PA a ∈ nonZeroDivisors O) (hd : ∀ u, PA u - PB u ∈ M₁ * Zr.map PA)
    (y : C) (n : ℕ) (x : R) (hx : x ∈ Zr ^ n) (hy : y * πC a ^ n = πC x) :
    F y - G y ∈ M₁ := by
  set E := Zr.map PA with hEdef
  have claim : ∀ n, ∀ x ∈ Zr ^ n, PA x - PB x ∈ M₁ * E ^ n := by
    intro n
    induction n with
    | zero =>
      intro x _
      rw [pow_zero, mul_one]
      exact (Ideal.mul_le_left (I := M₁) (J := E)) (hd x)
    | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro x hx z hz
        have e : PA (x * z) - PB (x * z) = PA x * (PA z - PB z) + (PA x - PB x) * PB z := by
          simp only [map_mul]; ring
        rw [e]
        refine add_mem ?_ ?_
        · have h1 : PA x ∈ E ^ n := by
            rw [hEdef, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx
          have hle : E ^ n * (M₁ * E) ≤ M₁ * E ^ (n + 1) := le_of_eq (by ring)
          exact hle (Ideal.mul_mem_mul h1 (hd z))
        · have h2 : PB z ∈ E := hE' (Ideal.mem_map_of_mem _ hz)
          have hle : M₁ * E ^ n * E ≤ M₁ * E ^ (n + 1) := le_of_eq (by ring)
          exact hle (Ideal.mul_mem_mul (ih x hx) h2)
      · intro u v hu hv
        have e : PA (u + v) - PB (u + v) = (PA u - PB u) + (PA v - PB v) := by
          simp only [map_add]; ring
        rw [e]; exact add_mem hu hv
  set t := PA a with htdef
  obtain ⟨m'', hm'', hxm⟩ : ∃ m'' ∈ M₁, m'' * t ^ n = PA x - PB x := by
    have := claim n x hx
    rw [hE, Ideal.span_singleton_pow, Ideal.mem_mul_span_singleton] at this
    exact this
  obtain ⟨m, hm, ham⟩ : ∃ m ∈ M₁, m * t = PA a - PB a := by
    have := hd a
    rw [hE, Ideal.mem_mul_span_singleton] at this
    exact this
  have hPB : PB a = (1 - m) * t := by rw [sub_mul, one_mul, ham]; ring
  have hFy : F y * t ^ n = PA x := by
    have := congrArg F hy
    rwa [map_mul, map_pow, hF, hF] at this
  have hGy : G y * ((1 - m) * t) ^ n = PB x := by
    have := congrArg G hy
    rwa [map_mul, map_pow, hG, hG, hPB] at this
  set r := 1 - (1 - m) ^ n with hrdef
  have hr : r ∈ M₁ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hrdef, map_sub, map_pow, map_sub, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hm, sub_zero, one_pow, sub_self]
  have key : (F y - G y + G y * r - m'') * t ^ n = 0 := by
    have h1 : (1 - m) ^ n = 1 - r := by rw [hrdef]; ring
    have h2 : G y * ((1 - r) * t ^ n) = PB x := by rw [← h1, ← mul_pow]; exact hGy
    linear_combination hFy - h2 - hxm
  have htn : t ^ n ∈ nonZeroDivisors O := pow_mem ht n
  have hz : F y - G y + G y * r - m'' = 0 :=
    (mul_right_mem_nonZeroDivisors_eq_zero_iff htn).mp key
  have : F y - G y = m'' - G y * r := by linear_combination hz
  rw [this]
  exact sub_mem hm'' (Ideal.mul_mem_left _ _ hr)

/-- Every neighbourhood of a point contains an affine neighbourhood of it. -/
private theorem exists_affineOpens_mem_le {X : Scheme.{u}} {x : X} {W : X.Opens} (hx : x ∈ W) :
    ∃ O : X.affineOpens, x ∈ O.1 ∧ O.1 ≤ W := by
  obtain ⟨O, hO, hxO, hle⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨⟨O, hO⟩, hxO, hle⟩

/-- A point of the blow-up lying over an affine open lies on one of its charts. -/
private theorem exists_mem_blowUpChartOpen {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (x : blowUp I) (hx : blowUpToBase I x ∈ U.1) :
    ∃ a : I.ideal U, x ∈ (blowUpChartOpen I U a).1 := by
  obtain ⟨a, ha⟩ := exists_mem_range_blowUpAffineChart_of_mem I U x hx
  refine ⟨a, ?_⟩
  rw [show (blowUpChartOpen I U a).1 = (blowUpAffineChart I U a).opensRange from
    Scheme.Hom.image_top_eq_opensRange _]
  exact ha

/-- Sections pulled back along two equal composites agree. -/
private theorem appLE_appLE_eq_of_comp_eq {X Y Y' Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') (U : Z.Opens) (V : Y.Opens) (V' : Y'.Opens)
    (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₁' : V' ≤ g' ⁻¹ᵁ U)
    (e₂' : W ≤ f' ⁻¹ᵁ V') (u : Γ(Z, U)) :
    f.appLE V W e₂ (g.appLE U V e₁ u) = f'.appLE V' W e₂' (g'.appLE U V' e₁' u) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (φ ψ : X ⟶ Z) (_ : φ = ψ) (e e'), φ.appLE U W e = ψ.appLE U W e' := by
    rintro _ _ rfl _ _; rfl
  rw [key _ _ h]

/-- A flat ring homomorphism maps non-zero-divisors to non-zero-divisors. -/
private theorem map_mem_nonZeroDivisors_of_flat {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) {r : A} (hr : r ∈ nonZeroDivisors A) : f r ∈ nonZeroDivisors B := by
  algebraize [f]
  have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) hr
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply this
  change r • x = r • (0 : B)
  rw [Algebra.smul_def, smul_zero, mul_comm]
  exact hx

/-- **The inductive step, for one blow-up.** Let `π : B_Z Y → Y` be the blow-up along `Z`,
`α, β : V → Y` with `α⁻¹Z = β⁻¹Z`, agreeing on `V(M)`, and `α_1, β_1 : V_1 → B_Z Y` over
`α ∘ p`, `β ∘ p` for some `p : V_1 → V`, with `α_1` flat. If `p^*M = M_1 · p^*(α⁻¹Z)`, then
`α_1` and `β_1` agree on `V(M_1)`. -/
private theorem eq_of_blowUp {Y V V₁ : Scheme.{u}} (Z : Y.IdealSheafData) (α β : V ⟶ Y)
    (hZ : Z.comap α = Z.comap β) (M : V.IdealSheafData)
    (hM : M.subschemeι ≫ α = M.subschemeι ≫ β) (p : V₁ ⟶ V) (α₁ β₁ : V₁ ⟶ blowUp Z)
    (hα₁ : α₁ ≫ blowUpToBase Z = p ≫ α) (hβ₁ : β₁ ≫ blowUpToBase Z = p ≫ β) [Flat α₁]
    (M₁ : V₁.IdealSheafData) (hM₁ : M.comap p = M₁ * (Z.comap α).comap p) :
    M₁.subschemeι ≫ α₁ = M₁.subschemeι ≫ β₁ := by
  set E := (Z.comap α).comap p with hEdef
  have hEα : E = (AlgebraicGeometry.exceptionalIdeal Z).comap α₁ := by
    rw [hEdef, AlgebraicGeometry.exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, hα₁]
  have hEβ : E = (AlgebraicGeometry.exceptionalIdeal Z).comap β₁ := by
    rw [hEdef, hZ, AlgebraicGeometry.exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, hβ₁]
  have hMle : M.comap p ≤ M₁ := by
    rw [hM₁]
    intro O
    exact (Ideal.mul_le_left (I := M₁.ideal O) (J := E.ideal O))
  apply eq_of_forall_appLE_sub_mem
  intro v hv
  have hw : p v ∈ M.support := by
    have h1 := Scheme.IdealSheafData.support_antitone hMle hv
    rwa [Scheme.IdealSheafData.support_comap] at h1
  have hαβw : α (p v) = β (p v) := by
    obtain ⟨q, hq⟩ : p v ∈ Set.range M.subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    rw [← hq, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hM]
  obtain ⟨U, hU⟩ := Stacks.Divisors.exists_affineOpens_mem (α (p v))
  have hα₁v : blowUpToBase Z (α₁ v) ∈ U.1 := by
    rw [← Scheme.Hom.comp_apply, hα₁, Scheme.Hom.comp_apply]; exact hU
  have hβ₁v : blowUpToBase Z (β₁ v) ∈ U.1 := by
    rw [← Scheme.Hom.comp_apply, hβ₁, Scheme.Hom.comp_apply, ← hαβw]; exact hU
  obtain ⟨a, ha⟩ := exists_mem_blowUpChartOpen Z U (α₁ v) hα₁v
  obtain ⟨a'', ha''⟩ := exists_mem_blowUpChartOpen Z U (β₁ v) hβ₁v
  obtain ⟨N, hwN, hNU⟩ : ∃ N : V.affineOpens, p v ∈ N.1 ∧ N.1 ≤ α ⁻¹ᵁ U.1 ⊓ β ⁻¹ᵁ U.1 :=
    exists_affineOpens_mem_le (W := α ⁻¹ᵁ U.1 ⊓ β ⁻¹ᵁ U.1)
      ⟨hU, show β (p v) ∈ U.1 from hαβw ▸ hU⟩
  have hNα : N.1 ≤ α ⁻¹ᵁ U.1 := hNU.trans inf_le_left
  have hNβ : N.1 ≤ β ⁻¹ᵁ U.1 := hNU.trans inf_le_right
  have hdiff : ∀ (O : V₁.affineOpens) (hOp : O.1 ≤ p ⁻¹ᵁ N.1) (u : Γ(Y, U.1)),
      p.appLE N.1 O.1 hOp (α.appLE U.1 N.1 hNα u) - p.appLE N.1 O.1 hOp (β.appLE U.1 N.1 hNβ u)
        ∈ M₁.ideal O * E.ideal O := by
    intro O hOp u
    change _ ∈ (M₁ * E).ideal O
    rw [← map_sub, ← hM₁,
      Scheme.IdealSheafData.ideal_comap_of_isAffineOpen M p N O hOp]
    exact Ideal.mem_map_of_mem _ (appLE_sub_mem_of_eq α β M hM N U.1 hNα hNβ u)
  have hEA : ∀ (O : V₁.affineOpens) (hOp : O.1 ≤ p ⁻¹ᵁ N.1),
      E.ideal O = (Z.ideal U).map (α.appLE U.1 N.1 hNα ≫ p.appLE N.1 O.1 hOp).hom := by
    intro O hOp
    rw [hEdef, Scheme.IdealSheafData.ideal_comap_of_isAffineOpen _ p N O hOp,
      Scheme.IdealSheafData.ideal_comap_of_isAffineOpen Z α U N hNα, Ideal.map_map]
    rfl
  have hEB : ∀ (O : V₁.affineOpens) (hOp : O.1 ≤ p ⁻¹ᵁ N.1),
      E.ideal O = (Z.ideal U).map (β.appLE U.1 N.1 hNβ ≫ p.appLE N.1 O.1 hOp).hom := by
    intro O hOp
    rw [hEdef, hZ, Scheme.IdealSheafData.ideal_comap_of_isAffineOpen _ p N O hOp,
      Scheme.IdealSheafData.ideal_comap_of_isAffineOpen Z β U N hNβ, Ideal.map_map]
    rfl
  have hEchart : ∀ (O : V₁.affineOpens) (b : Z.ideal U) (f : V₁ ⟶ blowUp Z)
      (hf : O.1 ≤ f ⁻¹ᵁ (blowUpChartOpen Z U b).1),
      E = (AlgebraicGeometry.exceptionalIdeal Z).comap f →
      E.ideal O = Ideal.span {f.appLE _ O.1 hf (blowUpChartMap Z U b (b : Γ(Y, U.1)))} := by
    intro O b f hf hE
    rw [hE, Scheme.IdealSheafData.ideal_comap_of_isAffineOpen _ f (blowUpChartOpen Z U b) O hf,
      ideal_exceptionalIdeal_blowUpChartOpen, Ideal.map_span, Set.image_singleton]
  have hcompα : ∀ (O : V₁.affineOpens) (hOC : O.1 ≤ α₁ ⁻¹ᵁ (blowUpChartOpen Z U a).1)
      (hOp : O.1 ≤ p ⁻¹ᵁ N.1) (u : Γ(Y, U.1)),
      α₁.appLE _ O.1 hOC (blowUpChartMap Z U a u) = p.appLE N.1 O.1 hOp (α.appLE U.1 N.1 hNα u) :=
    fun O hOC hOp u => appLE_appLE_eq_of_comp_eq hα₁ U.1 _ N.1 O.1 _ hOC hNα hOp u
  have hcompβ : ∀ (b : Z.ideal U) (O : V₁.affineOpens)
      (hOC : O.1 ≤ β₁ ⁻¹ᵁ (blowUpChartOpen Z U b).1)
      (hOp : O.1 ≤ p ⁻¹ᵁ N.1) (u : Γ(Y, U.1)),
      β₁.appLE _ O.1 hOC (blowUpChartMap Z U b u) = p.appLE N.1 O.1 hOp (β.appLE U.1 N.1 hNβ u) :=
    fun b O hOC hOp u => appLE_appLE_eq_of_comp_eq hβ₁ U.1 _ N.1 O.1 _ hOC hNβ hOp u
  have hgen : ∀ (O : V₁.affineOpens) (hOC : O.1 ≤ α₁ ⁻¹ᵁ (blowUpChartOpen Z U a).1)
      (hOp : O.1 ≤ p ⁻¹ᵁ N.1),
      E.ideal O = Ideal.span {p.appLE N.1 O.1 hOp (α.appLE U.1 N.1 hNα a)} ∧
        p.appLE N.1 O.1 hOp (α.appLE U.1 N.1 hNα a) ∈ nonZeroDivisors Γ(V₁, O.1) := by
    intro O hOC hOp
    rw [← hcompα O hOC hOp]
    exact ⟨hEchart O a α₁ hOC hEα, map_mem_nonZeroDivisors_of_flat _
      (HasRingHomProperty.appLE @Flat α₁ inferInstance _ O hOC)
      (blowUpChartMap_self_mem_nonZeroDivisors Z U a)⟩
  -- `β₁ v` lies on the chart at `a` as well
  have hβC : β₁ v ∈ (blowUpChartOpen Z U a).1 := by
    obtain ⟨O, hvO, hO⟩ : ∃ O : V₁.affineOpens, v ∈ O.1 ∧ O.1 ≤ α₁ ⁻¹ᵁ (blowUpChartOpen Z U a).1 ⊓
        β₁ ⁻¹ᵁ (blowUpChartOpen Z U a'').1 ⊓ p ⁻¹ᵁ N.1 :=
      exists_affineOpens_mem_le ⟨⟨ha, ha''⟩, hwN⟩
    have hOα : O.1 ≤ α₁ ⁻¹ᵁ (blowUpChartOpen Z U a).1 := hO.trans (inf_le_left.trans inf_le_left)
    have hOβ : O.1 ≤ β₁ ⁻¹ᵁ (blowUpChartOpen Z U a'').1 :=
      hO.trans (inf_le_left.trans inf_le_right)
    have hOp : O.1 ≤ p ⁻¹ᵁ N.1 := hO.trans inf_le_right
    obtain ⟨htE, ht⟩ := hgen O hOα hOp
    set t := p.appLE N.1 O.1 hOp (α.appLE U.1 N.1 hNα a) with ht_def
    set t' := p.appLE N.1 O.1 hOp (β.appLE U.1 N.1 hNβ a) with ht'_def
    set t'' := p.appLE N.1 O.1 hOp (β.appLE U.1 N.1 hNβ a'') with ht''_def
    obtain ⟨m, hm, hmt⟩ : ∃ m ∈ M₁.ideal O, m * t = t - t' := by
      have := hdiff O hOp a
      rw [htE, Ideal.mem_mul_span_singleton] at this
      exact this
    have hmem : blowUpChartMap Z U a'' (a : Γ(Y, U.1)) ∈
        Ideal.span {blowUpChartMap Z U a'' (a'' : Γ(Y, U.1))} := by
      rw [← ideal_exceptionalIdeal_blowUpChartOpen Z U a'', AlgebraicGeometry.exceptionalIdeal,
        ideal_comap_blowUpToBase_blowUpChartOpen Z Z U a'']
      exact Ideal.mem_map_of_mem _ a.2
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hmem
    have ht''E : E.ideal O = Ideal.span {t''} := by
      rw [hEchart O a'' β₁ hOβ hEβ, hcompβ a'' O hOβ hOp]
    obtain ⟨c, hc⟩ : ∃ c, c * t = t'' := by
      have : t'' ∈ E.ideal O := by rw [ht''E]; exact Ideal.mem_span_singleton_self t''
      rw [htE] at this
      exact Ideal.mem_span_singleton'.mp this
    have e1 : β₁.appLE _ O.1 hOβ h * t'' = t' := by
      have := congrArg (β₁.appLE _ O.1 hOβ) hh
      rwa [map_mul, hcompβ a'' O hOβ hOp, hcompβ a'' O hOβ hOp] at this
    have key : (1 - m - β₁.appLE _ O.1 hOβ h * c) * t = 0 := by
      linear_combination (-1 : Γ(V₁, O.1)) * hmt - e1 - (β₁.appLE _ O.1 hOβ h) * hc
    have h1m : 1 - m = β₁.appLE _ O.1 hOβ h * c :=
      sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff ht).mp key)
    have hv1 : v ∈ V₁.basicOpen (1 - m) := by
      have hvm : v ∉ V₁.basicOpen m :=
        (V₁.mem_zeroLocus_iff _ v).mp
          ((Scheme.IdealSheafData.mem_support_iff_of_mem hvO).mp hv) m hm
      rw [Scheme.mem_basicOpen V₁ _ v hvO] at hvm ⊢
      rw [map_sub, map_one]
      exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left hvm
    rw [h1m, Scheme.basicOpen_mul] at hv1
    have hv2 := hv1.1
    rw [Scheme.basicOpen_appLE] at hv2
    exact basicOpen_le_blowUpChartOpen Z U a'' a h hh.symm hv2.2
  obtain ⟨O, hvO, hO⟩ : ∃ O : V₁.affineOpens, v ∈ O.1 ∧ O.1 ≤ α₁ ⁻¹ᵁ (blowUpChartOpen Z U a).1 ⊓
      β₁ ⁻¹ᵁ (blowUpChartOpen Z U a).1 ⊓ p ⁻¹ᵁ N.1 :=
    exists_affineOpens_mem_le ⟨⟨ha, hβC⟩, hwN⟩
  have hOα : O.1 ≤ α₁ ⁻¹ᵁ (blowUpChartOpen Z U a).1 := hO.trans (inf_le_left.trans inf_le_left)
  have hOβ : O.1 ≤ β₁ ⁻¹ᵁ (blowUpChartOpen Z U a).1 := hO.trans (inf_le_left.trans inf_le_right)
  have hOp : O.1 ≤ p ⁻¹ᵁ N.1 := hO.trans inf_le_right
  obtain ⟨htE, ht⟩ := hgen O hOα hOp
  refine ⟨O, blowUpChartOpen Z U a, hOα, hOβ, hvO, fun y => ?_⟩
  obtain ⟨n, x, hx, hy⟩ := exists_mem_pow_mul_eq_blowUpChartMap Z U a y
  exact sub_mem_of_chart (blowUpChartMap Z U a).hom (α₁.appLE _ _ hOα).hom
    (β₁.appLE _ _ hOβ).hom (α.appLE U.1 N.1 hNα ≫ p.appLE N.1 O.1 hOp).hom
    (β.appLE U.1 N.1 hNβ ≫ p.appLE N.1 O.1 hOp).hom (fun u => hcompα O hOα hOp u)
    (fun u => hcompβ a O hOβ hOp u) (Z.ideal U) (M₁.ideal O) (a : Γ(Y, U.1))
    (by rw [← hEA O hOp, htE]; rfl) (by rw [← hEA O hOp, ← hEB O hOp])
    ht (fun u => by rw [← hEA O hOp]; exact hdiff O hOp u) y n x hx hy

/-- The composite `X_r → X_n` of the blow-ups after the `n`-th stage. -/
private noncomputable def seqRelBase : {X : Scheme.{u}} → (Q : ClosedBlowupSequence X) → (n : ℕ) →
    (Q.target ⟶ (Q.truncate n).target)
  | X, .nil _, _ => 𝟙 X
  | _, .cons Z Q, 0 => (ClosedBlowupSequence.cons Z Q).toBase
  | _, .cons _ Q, n + 1 => seqRelBase Q n

/-- The `n`-th centre `Z_n ⊆ X_n` of a blow-up sequence (`⊤` past its length). -/
private noncomputable def seqCentre : {X : Scheme.{u}} → (Q : ClosedBlowupSequence X) → (n : ℕ) →
    (Q.truncate n).target.IdealSheafData
  | _, .nil _, _ => ⊤
  | _, .cons Z _, 0 => Z
  | _, .cons _ Q, n + 1 => seqCentre Q n

/-- `seqRelBase` transported along an equality of sequences. -/
private theorem seqRelBase_congr {X : Scheme.{u}} {Q Q' : ClosedBlowupSequence X} (hQ : Q = Q')
    (n : ℕ) :
    eqToHom (congrArg ClosedBlowupSequence.target hQ) ≫ seqRelBase Q' n =
      seqRelBase Q n ≫ eqToHom (congrArg (fun Q => (Q.truncate n).target) hQ) := by
  subst hQ; simp

/-- `seqCentre` transported along an equality of sequences. -/
private theorem seqCentre_congr {X : Scheme.{u}} {Q Q' : ClosedBlowupSequence X} (hQ : Q = Q')
    (n : ℕ) :
    (seqCentre Q' n).comap (eqToHom (congrArg (fun Q => (Q.truncate n).target) hQ)) =
      seqCentre Q n := by
  subst hQ; simp

/-- Truncating a truncation at an earlier stage. -/
private theorem truncate_truncate_of_le {X : Scheme.{u}} (B : ClosedBlowupSequence X) {m n : ℕ}
    (h : n ≤ m) : (B.truncate m).truncate n = B.truncate n := by
  induction B generalizing m n with
  | nil X => rfl
  | cons Z B ih =>
    cases m with
    | zero =>
      obtain rfl : n = 0 := by omega
      rfl
    | succ m =>
      cases n with
      | zero => rfl
      | succ n =>
        simp only [ClosedBlowupSequence.truncate]
        rw [ih (by omega)]

/-- The composite of the blow-ups of a sequence is separated. -/
private theorem isSeparated_toBase {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    IsSeparated B.toBase := by
  induction B with
  | nil X => change IsSeparated (𝟙 X); infer_instance
  | cons Z B ih =>
    change IsSeparated (B.toBase ≫ blowUpToBase Z)
    have : IsSeparated (blowUpToBase Z) :=
      Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase _
    infer_instance

/-- `h_r : Y_r → X_r` is flat for flat `h`, being a base change of `h` (Kollár 3.30.1). -/
private theorem flat_pullbackHom {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X)
    [Flat h] : Flat (B.pullbackHom h) :=
  MorphismProperty.of_isPullback (P := @Flat) (Kollar.isPullback_pullback_toBase_of_flat B h) ‹_›

/-- The statement of `last_step` for a sequence `B` and indices `i`, `j = i + 1`. -/
private def LastStep {X : Scheme.{u}} (B : ClosedBlowupSequence X) (i j : ℕ) : Prop :=
  ∃ (Zc : (B.truncate i).target.IdealSheafData)
      (e : (B.truncate j).target ≅ blowUp Zc),
      ∀ {U : Scheme.{u}} (h : U ⟶ X)
        (c : (((B.truncate j).pullback h).truncate i).target =
          ((B.truncate i).pullback h).target),
        (B.truncate j).pullbackHom h ≫ e.hom ≫ blowUpToBase Zc =
            (seqRelBase ((B.truncate j).pullback h) i ≫ eqToHom c) ≫
              (B.truncate i).pullbackHom h ∧
          (Zc.comap ((B.truncate i).pullbackHom h)).comap (eqToHom c) =
            seqCentre ((B.truncate j).pullback h) i ∧
          ∀ (K : Option U.IdealSheafData) (a : ℕ)
            (J : ((B.truncate i).pullback h).target.IdealSheafData)
            (J₁ : ((B.truncate j).pullback h).target.IdealSheafData),
            ((B.truncate i).pullback h).derivedTransform K a = some J →
            ((B.truncate j).pullback h).derivedTransform K a = some J₁ →
            J.comap (seqRelBase ((B.truncate j).pullback h) i ≫ eqToHom c) =
              J₁ * ((Zc.comap ((B.truncate i).pullbackHom h)).comap
                (seqRelBase ((B.truncate j).pullback h) i ≫ eqToHom c)) ^ a

/-- `LastStep` at the first blow-up. -/
private theorem lastStep_zero {X : Scheme.{u}} (Z₀ : X.IdealSheafData)
    (B₀ : ClosedBlowupSequence (blowUp Z₀)) : LastStep (.cons Z₀ B₀) 0 1 := by
  cases B₀ <;>
  · refine ⟨Z₀, Iso.refl _, @fun U h c => ⟨?_, ?_, ?_⟩⟩
    · rw [show eqToHom c = 𝟙 U from rfl]
      change canonicalLift h Z₀ ≫ 𝟙 _ ≫ blowUpToBase Z₀ =
        ((𝟙 _ ≫ blowUpToBase (Z₀.comap h)) ≫ 𝟙 U) ≫ h
      simp only [Category.id_comp, Category.comp_id]
      exact canonicalLift_comp_blowUpToBase h Z₀
    · rw [show eqToHom c = 𝟙 U from rfl]
      change (Z₀.comap h).comap (𝟙 U) = Z₀.comap h
      exact Scheme.IdealSheafData.comap_id _
    · intro K a J J₁ hJ hJ₁
      cases hJ
      rw [show eqToHom c = 𝟙 U from rfl]
      revert J₁
      dsimp only [ClosedBlowupSequence.truncate, ClosedBlowupSequence.pullback,
        ClosedBlowupSequence.target, ClosedBlowupSequence.pullbackHom, seqRelBase,
        ClosedBlowupSequence.toBase, ClosedBlowupSequence.derivedTransform]
      intro J₁ hJ₁
      have key := ClosedBlowupSequence.derivedTransformStep_mul_eq (Z₀.comap h) a J J₁ hJ₁
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _)
      simp only [Category.id_comp, Category.comp_id]
      exact key.symm

/-- **The last blow-up of a truncation.** `X_{i+1} = B_{Z_i} X_i`, and for every `h : U → X`,
with `p : U_{i+1} → U_i`: `π ∘ h_{i+1} = h_i ∘ p`, the `i`-th centre of `h^*𝐁` is `h_i⁻¹Z_i`, and
`p^*T_i = T_{i+1} · p^*(h_i⁻¹Z_i)^a` for the transforms `T_l = T_l(K, a)` along `h^*𝐁`. -/
private theorem last_step {X : Scheme.{u}} (B : ClosedBlowupSequence X) (i : ℕ)
    (hi : i < B.length) : LastStep B i (i + 1) := by
  induction B generalizing i with
  | nil X => exact absurd hi (Nat.not_lt_zero _)
  | cons Z₀ B₀ ih =>
    cases i with
    | zero => exact lastStep_zero Z₀ B₀
    | succ k =>
      obtain ⟨Zc, e, H⟩ := ih k (Nat.lt_of_succ_lt_succ hi)
      refine ⟨Zc, e, fun h c => ?_⟩
      obtain ⟨h1, h2, h3⟩ := H (canonicalLift h Z₀) c
      refine ⟨h1, h2, ?_⟩
      dsimp only [ClosedBlowupSequence.truncate, ClosedBlowupSequence.pullback,
        ClosedBlowupSequence.target, ClosedBlowupSequence.pullbackHom, seqRelBase,
        ClosedBlowupSequence.derivedTransform]
      intro K a J J₁ hJ hJ₁
      exact h3 _ a J J₁ hJ hJ₁

namespace ClosedBlowupSequence

/-- **The étale equivalence lifts through a blow-up** (Kollár, proof of Thm. 3.97). Let
`𝐁, 𝐁'` be smooth blow-up sequences of order `m = maxord I ≥ 1` starting with `(X, I)`, étale
equivalent via `ψ, ψ' : U → X` (`IsEtaleChartPair`, `B.pullback ψ = B'.pullback ψ'`), and let
`i < r` with `B.truncate l = B'.truncate l` for all `l ≤ i + 1`. If
`(ψ_i, ψ'_i)^*I_{Δ_{X_i}} ⊆ M_i = T_i(D^{m-1}(ψ^*I), 1)`, then `M_{i+1}` is an ideal sheaf and
`(ψ_{i+1}, ψ'_{i+1})^*I_{Δ_{X_{i+1}}} ⊆ M_{i+1}`. -/
@[mmp "lem_kr3d_etale_equivalence_lifts_through_blowup"]
public theorem ker_diagonal_comap_le_derivedTransform_succ {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    [IsSeparated sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (I : X.IdealSheafData) (hI : IsNonzeroAtGenericPoints I) (m : ℕ) (hm : maxOrder I = m)
    (hm1 : 1 ≤ m) (B B' : ClosedBlowupSequence X) (hB : B.IsOrderMPlainSeq sX I m)
    (hB' : B'.IsOrderMPlainSeq sX I m)
    {U : Scheme.{u}} (sU : U ⟶ Spec (.of k)) (ψ ψ' : U ⟶ X) (hψ : IsEtaleChartPair sX I sU ψ ψ')
    (hBB' : B.pullback ψ = B'.pullback ψ') (i : ℕ) (hi : i < B.length)
    (hZ : ∀ l ≤ i + 1, B.truncate l = B'.truncate l) :
    let hU : ∀ l ≤ i + 1, (B.truncate l).pullback ψ = (B.truncate l).pullback ψ' := fun l hl => by
      rw [← Kollar.pullback_truncate, hBB', Kollar.pullback_truncate, hZ l hl]
    let ψl : ∀ l, ((B.truncate l).pullback ψ).target ⟶ (B.truncate l).target :=
      fun l => (B.truncate l).pullbackHom ψ
    let ψl' : ∀ l ≤ i + 1, ((B.truncate l).pullback ψ).target ⟶ (B.truncate l).target :=
      fun l hl => eqToHom (congrArg target (hU l hl)) ≫ (B.truncate l).pullbackHom ψ'
    let hcomm : ∀ l (hl : l ≤ i + 1),
        ψl l ≫ (B.truncate l).toBase ≫ sX = ψl' l hl ≫ (B.truncate l).toBase ≫ sX := by
      intro l hl
      have key : ∀ {P P' : ClosedBlowupSequence U} (h : P = P'),
          eqToHom (congrArg target h) ≫ P'.toBase = P.toBase := by
        rintro P _ rfl; simp
      simp only [ψl, ψl', Category.assoc]
      rw [reassoc_of% Kollar.pullbackHom_toBase_comm, reassoc_of% Kollar.pullbackHom_toBase_comm,
        reassoc_of% key (hU l hl), hψ.comp_eq, hψ.comp_eq']
    let M : ∀ l, Option ((B.truncate l).pullback ψ).target.IdealSheafData := fun l =>
      ((B.truncate l).pullback ψ).derivedTransform
        (some (higherDerivativeIdeal sU (I.comap ψ) (m - 1))) 1
    (∀ Mi, M i = some Mi →
        (pullback.diagonal ((B.truncate i).toBase ≫ sX)).ker.comap
          (pullback.lift (ψl i) (ψl' i (Nat.le_succ i)) (hcomm i (Nat.le_succ i))) ≤ Mi) →
      ∃ Mi1, M (i + 1) = some Mi1 ∧
        (pullback.diagonal ((B.truncate (i + 1)).toBase ≫ sX)).ker.comap
          (pullback.lift (ψl (i + 1)) (ψl' (i + 1) le_rfl) (hcomm (i + 1) le_rfl)) ≤ Mi1 := by
  intro hU ψl ψl' hcomm M hMi
  have := hψ.locallyOfFiniteType
  have := hψ.quasiCompact
  have := hψ.etale
  -- `M_l = T_l(D^{m-1}(ψ^*I), 1)` is an ideal sheaf for `l ≤ i + 1`: Corollary 3.77 for the
  -- pull-back `ψ^*𝐁`, which is of order `≥ m` for `(ψ^*I, m)`.
  have h_some : ∀ l ≤ i + 1, ∃ Ml, M l = some Ml := by
    intro l hl
    have hU := equidimensional_of_etale sX hX hdim ψ
    obtain ⟨hP, -⟩ := isOrderGePlainSeq_pullback_of_etale sX
      (isSmoothScheme_of_isOrderMPlainSeq hB) hX I hI m hm1 hm.le B hB ψ
    rw [hψ.comp_eq] at hP
    have h := (isOrderGePlainSeq_higherDerivativeIdeal sU hU.1 hU.2 ⟨I.comap ψ, m⟩
      (isNonzeroAtGenericPoints_comap_of_flat ψ hI) (B.pullback ψ) hP (m - 1)
      (Nat.sub_le _ _)).2 l (by rw [length_pullback]; omega)
    have hm' : m - (m - 1) = 1 := by omega
    rw [Kollar.pullback_truncate] at h
    simp only [derivedTransformJ, hm'] at h
    exact ⟨_, h⟩
  obtain ⟨Mi, hMiEq⟩ := h_some i (Nat.le_succ i)
  obtain ⟨Mi1, hMi1Eq⟩ := h_some (i + 1) le_rfl
  refine ⟨Mi1, hMi1Eq, ?_⟩
  -- the last blow-up `X_{i+1} → X_i`, along `Z_i`, and its pull-backs
  obtain ⟨Zc, e, H⟩ := last_step B i hi
  have hc : ∀ {U' : Scheme.{u}} (h : U' ⟶ X),
      (((B.truncate (i + 1)).pullback h).truncate i).target =
        ((B.truncate i).pullback h).target := fun h => by
    rw [Kollar.pullback_truncate, truncate_truncate_of_le B (Nat.le_succ i)]
  obtain ⟨h1, h2, h3⟩ := H ψ (hc ψ)
  obtain ⟨h1', h2', -⟩ := H ψ' (hc ψ')
  -- `ψ_i` and `ψ'_i` agree on `V(M_i)`
  have : IsSeparated ((B.truncate i).toBase ≫ sX) := by
    have := isSeparated_toBase (B.truncate i)
    infer_instance
  have hMeq : Mi.subschemeι ≫ ψl i = Mi.subschemeι ≫ ψl' i (Nat.le_succ i) :=
    eq_of_ker_diagonal_comap_le _ _ (hcomm i (Nat.le_succ i)) Mi (hMi Mi hMiEq)
  -- `Z^U_i = ψ_i⁻¹Z_i = ψ'_i⁻¹Z_i`
  have hZc : Zc.comap (ψl i) = Zc.comap (ψl' i (Nat.le_succ i)) := by
    have e1 : Zc.comap (ψl i) =
        (seqCentre ((B.truncate (i + 1)).pullback ψ) i).comap (eqToHom (hc ψ).symm) := by
      rw [← h2, ← Scheme.IdealSheafData.comap_comp, eqToHom_trans, eqToHom_refl,
        Scheme.IdealSheafData.comap_id]
    have e2 : Zc.comap (ψl' i (Nat.le_succ i)) =
        (seqCentre ((B.truncate (i + 1)).pullback ψ) i).comap (eqToHom (hc ψ).symm) := by
      rw [← seqCentre_congr (hU (i + 1) le_rfl) i, ← h2']
      simp only [ψl', ← Scheme.IdealSheafData.comap_comp, eqToHom_trans_assoc]
    exact e1.trans e2.symm
  have : Flat ((B.truncate (i + 1)).pullbackHom ψ) := flat_pullbackHom _ ψ
  have : Flat (ψl (i + 1) ≫ e.hom) := by
    change Flat ((B.truncate (i + 1)).pullbackHom ψ ≫ e.hom)
    infer_instance
  have hα₁ : (ψl (i + 1) ≫ e.hom) ≫ blowUpToBase Zc =
      (seqRelBase ((B.truncate (i + 1)).pullback ψ) i ≫ eqToHom (hc ψ)) ≫ ψl i := by
    rwa [Category.assoc]
  have hβ₁ : (ψl' (i + 1) le_rfl ≫ e.hom) ≫ blowUpToBase Zc =
      (seqRelBase ((B.truncate (i + 1)).pullback ψ) i ≫ eqToHom (hc ψ)) ≫
        ψl' i (Nat.le_succ i) := by
    simp only [ψl', Category.assoc]
    rw [h1']
    simp only [Category.assoc]
    rw [← Category.assoc (eqToHom _) (seqRelBase _ i), seqRelBase_congr (hU (i + 1) le_rfl) i]
    simp only [Category.assoc, eqToHom_trans_assoc]
  have hM₁ : Mi.comap (seqRelBase ((B.truncate (i + 1)).pullback ψ) i ≫ eqToHom (hc ψ)) =
      Mi1 * (Zc.comap (ψl i)).comap
        (seqRelBase ((B.truncate (i + 1)).pullback ψ) i ≫ eqToHom (hc ψ)) := by
    simpa only [pow_one] using h3 _ 1 Mi Mi1 hMiEq hMi1Eq
  have key := eq_of_blowUp Zc (ψl i) (ψl' i (Nat.le_succ i)) hZc Mi hMeq _
    (ψl (i + 1) ≫ e.hom) (ψl' (i + 1) le_rfl ≫ e.hom) hα₁ hβ₁ Mi1 hM₁
  refine ker_diagonal_comap_le_of_eq _ _ (hcomm (i + 1) le_rfl) Mi1 ?_
  rw [← cancel_mono e.hom]
  simpa only [Category.assoc] using key

end ClosedBlowupSequence

end EtaleEquivalence

/-! ### Étale realization of the formal equivalence -/

section EtaleRealization

open IsLocalRing

/-- The two projections of `pullback a a'` agree over the base when `a` and `a'` are both
maps over the same base. -/
private lemma fst_comp_eq_snd_comp {Y S : Scheme.{u}} (f : Y ⟶ S) {n : Type u}
    (v v' : n → Γ(Y, ⊤)) :
    pullback.fst (AffineSpace.homOfVector f v) (AffineSpace.homOfVector f v') ≫ f =
      pullback.snd _ _ ≫ f := by
  simpa only [Category.assoc, AffineSpace.homOfVector_over] using
    pullback.condition (f := AffineSpace.homOfVector f v) (g := AffineSpace.homOfVector f v') =≫
      (𝔸(n; S) ↘ S)

/-- Equality of pulled-back ideal sheaves along `U.ι ≫ f` and `U.ι ≫ g`, from equality of the
stalks of the pull-backs along `f` and `g` at the points of `U`. -/
private lemma comap_comp_eq_of_stalk_eq {W X : Scheme.{u}} (f g : W ⟶ X)
    (A B : X.IdealSheafData) (U : W.Opens)
    (h : ∀ u : U.toScheme,
      IdealSheafData.stalk (A.comap f) (U.ι u) = IdealSheafData.stalk (B.comap g) (U.ι u)) :
    A.comap (U.ι ≫ f) = B.comap (U.ι ≫ g) := by
  rw [Scheme.IdealSheafData.comap_comp A U.ι f, Scheme.IdealSheafData.comap_comp B U.ι g]
  refine IdealSheafData.eq_of_stalk_eq _ _ fun u ↦ ?_
  rw [IdealSheafData.stalk_comap (A.comap f) U.ι u, IdealSheafData.stalk_comap (B.comap g) U.ι u,
    h u]

open KaehlerDifferential in
/-- A formally smooth `R`-algebra `B` whose module of differentials has the basis `d b_i` is
formally étale over `R[X_i]` via `X_i ↦ b_i`. -/
private theorem formallyEtale_mvPolynomial_of_basis {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FormallySmooth R B] {ι : Type u} (b : ι → B)
    (β : Module.Basis ι B Ω[B⁄R]) (hβ : ∀ i, β i = D R B (b i)) :
    letI := (MvPolynomial.aeval (R := R) b).toRingHom.toAlgebra
    Algebra.FormallyEtale (MvPolynomial ι R) B := by
  classical
  let := (MvPolynomial.aeval (R := R) b).toRingHom.toAlgebra
  have hT : IsScalarTower R (MvPolynomial ι R) B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = MvPolynomial.aeval b (MvPolynomial.C r)
      simp
  have hX : ∀ i, algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) = b i := fun i ↦ by
    change MvPolynomial.aeval b (MvPolynomial.X i) = b i
    simp
  have hbij : Function.Bijective (Finsupp.linearCombination B (fun i ↦ D R B (b i))) := by
    have : (fun i ↦ D R B (b i)) = ⇑β := funext fun i ↦ (hβ i).symm
    rw [this]
    have h2 : (Finsupp.linearCombination B ⇑β) = β.repr.symm.toLinearMap := by
      ext v
      simp
    rw [h2]
    exact β.repr.symm.bijective
  have heq : mapBaseChange R (MvPolynomial ι R) B =
      (Finsupp.linearCombination B (fun i ↦ D R B (b i))) ∘ₗ
        (Algebra.TensorProduct.basis B (mvPolynomialBasis R ι)).repr.toLinearMap := by
    apply (Algebra.TensorProduct.basis B (mvPolynomialBasis R ι)).ext
    intro i
    simp [Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply, hX]
  have hF : Function.Bijective (mapBaseChange R (MvPolynomial ι R) B) := by
    rw [heq]
    exact hbij.comp (Algebra.TensorProduct.basis B (mvPolynomialBasis R ι)).repr.bijective
  refine (Algebra.formallyEtale_iff _ B).mpr ⟨?_, ?_⟩
  · refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨u, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) B x
    obtain ⟨w, rfl⟩ := hF.2 u
    exact (KaehlerDifferential.exact_mapBaseChange_map R (MvPolynomial ι R) B).apply_apply_eq_zero w
  · refine subsingleton_of_forall_eq 0 fun z ↦ ?_
    have : Subsingleton (Algebra.H1Cotangent R B) := Algebra.FormallySmooth.subsingleton_h1Cotangent
    obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ R (MvPolynomial ι R) B z).mp
      (hF.1 (by rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange R (MvPolynomial ι R) B _).mpr
        ⟨z, rfl⟩, map_zero]))
    rw [← hw, Subsingleton.elim w 0, map_zero]

/-- Local coordinates on an affine open `V` of a smooth `k`-scheme give an étale map
`V ⟶ 𝔸ⁿ_k`. -/
private theorem etale_homOfVector_of_isLocalCoordinatesOn {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] {V : X.Opens} (hV : IsAffineOpen V)
    {N : ℕ} {z : Fin N → Γ(X, V)} (hz : IsLocalCoordinatesOn sX V z) :
    Etale (AffineSpace.homOfVector (V.ι ≫ sX)
      (fun i : ULift.{u} (Fin N) ↦ V.topIso.inv (z i.down))) := by
  classical
  let := MMP.Mori.sectionAlgebra sX V
  have hsm := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra sX hV
  obtain ⟨β, hβ⟩ := hz ⟨V, hV⟩ le_rfl
  let b : ULift.{u} (Fin N) → Γ(X, V) := fun i ↦ z i.down
  let β' := β.reindex Equiv.ulift.symm
  have hβ' : ∀ i, β' i = KaehlerDifferential.D k _ (b i) := fun i ↦ by
    simp only [β', Module.Basis.reindex_apply, Equiv.symm_symm, hβ, b, restrictSection]
    rw [MMP.Flips.ResolutionInputs.presheaf_map_homOfLE_self]
    rfl
  have hfe := formallyEtale_mvPolynomial_of_basis b β' hβ'
  let := (MvPolynomial.aeval (R := k) b).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin N)) k) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = MvPolynomial.aeval b (MvPolynomial.C r)
      simp
  have : Algebra.FinitePresentation (MvPolynomial (ULift.{u} (Fin N)) k) Γ(X, V) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k _ _
  have het : (MvPolynomial.aeval (R := k) b).toRingHom.Etale := ⟨hfe, inferInstance⟩
  let φ : MvPolynomial (ULift.{u} (Fin N)) Γ(Spec (.of k), ⊤) →+* Γ(X, V) :=
    (MvPolynomial.aeval (R := k) b).toRingHom.comp
      (MvPolynomial.map (Scheme.ΓSpecIso (.of k)).hom.hom)
  refine MMP.Flips.ResolutionInputs.etale_homOfVector_of_etale sX V hV b φ ?_ ?_ ?_
  · ext r
    simp only [φ, RingHom.comp_apply, MvPolynomial.map_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, MvPolynomial.aeval_C]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ V _).hom
      ((Scheme.ΓSpecIso (.of k)).hom.hom r) = _
    rw [← CommRingCat.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · intro i
    simp [φ, b]
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (MvPolynomial.mapEquiv (ULift.{u} (Fin N))
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv).bijective) het

/-- If a finitely generated ideal `I` maps into `J S` in a localization `S = M⁻¹A`, then some
`m ∈ M` satisfies `m • I ≤ J`. -/
private lemma exists_mem_mul_mem_of_map_le {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] {I J : Ideal A} (hI : I.FG)
    (h : I.map (algebraMap A S) ≤ J.map (algebraMap A S)) :
    ∃ m ∈ M, ∀ a ∈ I, m * a ∈ J := by
  classical
  obtain ⟨T, rfl⟩ := hI
  have key : ∀ t ∈ T, ∃ m ∈ M, m * t ∈ J := fun t ht ↦
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M (S := S) J t).mp
      (h (Ideal.mem_map_of_mem _ (Ideal.subset_span ht)))
  choose! m hmM hmJ using key
  refine ⟨∏ t ∈ T, m t, prod_mem fun t ht ↦ hmM t ht, fun a ha ↦ ?_⟩
  induction ha using Submodule.span_induction with
  | mem t ht =>
    rw [← Finset.mul_prod_erase T m ht, mul_comm (m t), mul_assoc]
    exact J.mul_mem_left _ (hmJ t ht)
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact J.add_mem ha hb
  | smul c a _ ha => rw [smul_eq_mul, mul_left_comm]; exact J.mul_mem_left c ha

/-- On an affine open `V ∋ x` of a locally Noetherian scheme, a finitely generated ideal of
sections whose germs at `x` lie in the stalk of `B` lies in `B` after multiplying by some
section `s` invertible at `x`. -/
private lemma exists_basicOpen_mul_mem {X : Scheme.{u}} [IsLocallyNoetherian X]
    (B : X.IdealSheafData) {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hxV : x ∈ V)
    (J : Ideal Γ(X, V))
    (h : J.map (X.presheaf.germ V x hxV).hom ≤ IdealSheafData.stalk B x) :
    ∃ s : Γ(X, V), x ∈ X.basicOpen s ∧ ∀ a ∈ J, s * a ∈ B.ideal ⟨V, hV⟩ := by
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxV).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  rw [IdealSheafData.stalk_eq_map_germ B x ⟨V, hV⟩ hxV] at h
  obtain ⟨s, hsM, hs⟩ := exists_mem_mul_mem_of_map_le (S := X.presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (IsNoetherian.noetherian J) h
  exact ⟨s, (Scheme.mem_basicOpen _ _ _ hxV).mpr
    (IsLocalization.map_units _ (⟨s, hsM⟩ : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)), hs⟩

/-- A containment of stalks of ideal sheaves on a locally Noetherian scheme spreads out to a
neighbourhood. -/
private lemma exists_open_stalk_le {X : Scheme.{u}} [IsLocallyNoetherian X]
    (A B : X.IdealSheafData) (x : X)
    (h : IdealSheafData.stalk A x ≤ IdealSheafData.stalk B x) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, IdealSheafData.stalk A y ≤ IdealSheafData.stalk B y := by
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  rw [IdealSheafData.stalk_eq_map_germ A x ⟨V, hV⟩ hxV] at h
  obtain ⟨s, hxs, hs⟩ := exists_basicOpen_mul_mem B hV hxV _ h
  refine ⟨X.basicOpen s, hxs, fun y hy ↦ ?_⟩
  have hyV : y ∈ V := X.basicOpen_le s hy
  rw [IdealSheafData.stalk_eq_map_germ A y ⟨V, hV⟩ hyV,
    IdealSheafData.stalk_eq_map_germ B y ⟨V, hV⟩ hyV, Ideal.map_le_iff_le_comap]
  intro a ha
  have hu : IsUnit ((X.presheaf.germ V y hyV).hom s) := (Scheme.mem_basicOpen _ _ _ hyV).mp hy
  rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul]
  exact Ideal.mem_map_of_mem _ (hs a ha)

/-- Ideals of a Noetherian local ring are recovered from their extensions to the completion. -/
private lemma comap_map_adicCompletion {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) = I := by
  have := AdicCompletion.flat_of_isNoetherian (maximalIdeal R) (R := R)
  have : Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- The stalk map of `f` at `w`, read from the stalk at a point `p` equal to `f w`. -/
private noncomputable abbrev stalkHomOfEq {W X : Scheme.{u}} (f : W ⟶ X) (w : W) {p : X}
    (h : f w = p) :
    X.presheaf.stalk p ⟶ W.presheaf.stalk w :=
  eqToHom (by rw [h]) ≫ f.stalkMap w

/-- An étale morphism inducing an isomorphism of residue fields at `w` identifies the completed
local rings at `p = f w` and at `w`, compatibly with the stalk map and the maximal ideals. -/
private lemma exists_completion_ringEquiv {W X : Scheme.{u}} (f : W ⟶ X) [Etale f] (w : W)
    [IsIso (f.residueFieldMap w)] {p : X} (h : f w = p) :
    ∃ e : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃+*
        AdicCompletion (maximalIdeal (W.presheaf.stalk w)) (W.presheaf.stalk w),
      e.toRingHom.comp (algebraMap _ _) =
          (algebraMap _ _).comp (stalkHomOfEq f w h).hom ∧
        ((maximalIdeal (X.presheaf.stalk p)).map (algebraMap _ _)).map e.toRingHom =
          (maximalIdeal (W.presheaf.stalk w)).map (algebraMap _ _) := by
  subst h
  have he := MMP.Foundations.completedStalkRingEquiv_comp_algebraMap f w
  refine ⟨MMP.Foundations.completedStalkRingEquiv f w, by simpa using he, ?_⟩
  algebraize [(f.stalkMap w).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f w)) (W.presheaf.stalk w)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap w).hom
  have : Algebra.EssFiniteType (X.presheaf.stalk (f w)) (W.presheaf.stalk w) :=
    (RingHom.essFiniteType_algebraMap).mp (LocallyOfFiniteType.stalkMap f w)
  have : Algebra.FormallyUnramified (X.presheaf.stalk (f w)) (W.presheaf.stalk w) :=
    (RingHom.formallyUnramified_algebraMap).mp (FormallyUnramified.stalkMap f w)
  have hm := Algebra.FormallyUnramified.map_maximalIdeal
    (R := X.presheaf.stalk (f w)) (S := W.presheaf.stalk w)
  rw [Ideal.map_map,
    show (MMP.Foundations.completedStalkRingEquiv f w).toRingHom.comp _ = _ from he,
    ← Ideal.map_map]
  exact congrArg _ hm

/-- The completion of a pulled-back ideal sheaf is the image of the completed ideal. -/
private lemma completedIdeal_comap {W X : Scheme.{u}} (f : W ⟶ X) (w : W) {p : X}
    (h : f w = p) (J : X.IdealSheafData)
    (e : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃+*
        AdicCompletion (maximalIdeal (W.presheaf.stalk w)) (W.presheaf.stalk w))
    (he : e.toRingHom.comp (algebraMap _ _) =
          (algebraMap _ _).comp (stalkHomOfEq f w h).hom) :
    completedIdeal (J.comap f) w = (completedIdeal J p).map e.toRingHom := by
  subst h
  simp only [stalkHomOfEq, eqToHom_refl, Category.id_comp] at he
  rw [completedIdeal, completedIdeal, IdealSheafData.stalk_comap, Ideal.map_map, Ideal.map_map, he]

/-- Two identifications `e₁, e₂` of the completed local rings at `p` and at `w` which carry the
completed ideals of `J₁` and `J₂` to the same ideal identify the stalks at `w` of their
pull-backs. -/
private lemma stalk_comap_eq_of_map_completedIdeal_eq {W X : Scheme.{u}} [IsLocallyNoetherian W]
    (f₁ f₂ : W ⟶ X) {w : W} {p : X} (h₁ : f₁ w = p) (h₂ : f₂ w = p) (J₁ J₂ : X.IdealSheafData)
    (e₁ e₂ : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃+*
        AdicCompletion (maximalIdeal (W.presheaf.stalk w)) (W.presheaf.stalk w))
    (he₁ : e₁.toRingHom.comp (algebraMap _ _) = (algebraMap _ _).comp (stalkHomOfEq f₁ w h₁).hom)
    (he₂ : e₂.toRingHom.comp (algebraMap _ _) = (algebraMap _ _).comp (stalkHomOfEq f₂ w h₂).hom)
    (hJ : (completedIdeal J₁ p).map e₁.toRingHom = (completedIdeal J₂ p).map e₂.toRingHom) :
    IdealSheafData.stalk (J₁.comap f₁) w = IdealSheafData.stalk (J₂.comap f₂) w := by
  rw [← comap_map_adicCompletion (IdealSheafData.stalk (J₁.comap f₁) w),
    ← comap_map_adicCompletion (IdealSheafData.stalk (J₂.comap f₂) w)]
  congr 1
  change completedIdeal (J₁.comap f₁) w = completedIdeal (J₂.comap f₂) w
  rw [completedIdeal_comap f₁ w h₁ J₁ e₁ he₁, completedIdeal_comap f₂ w h₂ J₂ e₂ he₂, hJ]

/-- The germ of `V.topIso.inv z` at a point of `V` is the image of the germ of `z`. -/
private lemma germ_topIso_inv {X : Scheme.{u}} {V : X.Opens} (q : V.toScheme) (hq : V.ι q ∈ V)
    (z : Γ(X, V)) :
    (V.ι.stalkMap q).hom ((X.presheaf.germ V (V.ι q) hq).hom z) =
      (V.toScheme.presheaf.germ ⊤ q trivial).hom (V.topIso.inv.hom z) := by
  have h1 := Scheme.Hom.germ_stalkMap_apply V.ι V q hq z
  have h2 := TopCat.Presheaf.germ_res_apply V.toScheme.presheaf
    (homOfLE (le_top : V.ι ⁻¹ᵁ V ≤ ⊤)) q hq (V.topIso.inv.hom z)
  rw [h1, MMP.Flips.ResolutionInputs.iota_app_self_eq, h2]

/-- Germs of pulled-back coordinates. -/
private lemma stalkHomOfEq_germ {W X : Scheme.{u}} {V : X.Opens} (f : W ⟶ V.toScheme) (w : W)
    {p : X} (h : (f ≫ V.ι) w = p) (hpV : p ∈ V) (z : Γ(X, V)) :
    (stalkHomOfEq (f ≫ V.ι) w h).hom ((X.presheaf.germ V p hpV).hom z) =
      (W.presheaf.germ ⊤ w trivial).hom (f.appTop.hom (V.topIso.inv.hom z)) := by
  subst h
  simp only [stalkHomOfEq, eqToHom_refl, Scheme.Hom.stalkMap_comp]
  exact (congrArg (f.stalkMap w).hom (germ_topIso_inv (f w) hpV z)).trans
    (Scheme.Hom.germ_stalkMap_apply f ⊤ w trivial _)

/-- The stalk maps of a morphism over `k` are `k`-algebra maps. -/
private lemma stalkHomOfEq_algebraMap {k : Type u} [Field k] {W X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f : W ⟶ X) (w : W) {p : X} (h : f w = p) (c : k) :
    (stalkHomOfEq f w h).hom (letI := MMP.Mori.stalkAlgebra sX p; algebraMap k _ c) =
      (letI := MMP.Mori.stalkAlgebra (f ≫ sX) w; algebraMap k _ c) := by
  subst h
  simp only [stalkHomOfEq, eqToHom_refl, Category.id_comp,
    RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.comp_appTop]
  rfl

/-- Composing with the stalk map at the closed point of `Spec K`. -/
private lemma stalkClosedPointTo_stalkHomOfEq {K : Type u} [Field K] {W X : Scheme.{u}}
    (t : Spec (.of K) ⟶ W) (f : W ⟶ X) {p : X} (h : f (t (closedPoint K)) = p)
    (s : X.presheaf.stalk p) :
    (Scheme.stalkClosedPointTo t).hom ((stalkHomOfEq f _ h).hom s) =
      (Scheme.stalkClosedPointTo (t ≫ f)).hom
        ((eqToHom (by subst h; rfl) : X.presheaf.stalk p ⟶
          X.presheaf.stalk ((t ≫ f) (closedPoint K))).hom s) := by
  subst h
  rw [Scheme.stalkClosedPointTo_comp]
  rfl

private lemma stalkClosedPointTo_congr {K : Type u} [Field K] {X : Scheme.{u}}
    {F G : Spec (.of K) ⟶ X} (hFG : F = G) {p : X} (hF : F (closedPoint K) = p)
    (hG : G (closedPoint K) = p) (s : X.presheaf.stalk p) :
    (Scheme.stalkClosedPointTo F).hom
        ((eqToHom (by subst hF; rfl) : X.presheaf.stalk p ⟶
          X.presheaf.stalk (F (closedPoint K))).hom s) =
      (Scheme.stalkClosedPointTo G).hom
        ((eqToHom (by subst hG; rfl) : X.presheaf.stalk p ⟶
          X.presheaf.stalk (G (closedPoint K))).hom s) := by
  subst hFG
  rfl

/-- Two morphisms agreeing on a `K`-point induce stalk maps agreeing modulo the maximal ideal. -/
private lemma sub_mem_maximalIdeal_of_comp_eq {K : Type u} [Field K] {W X : Scheme.{u}}
    (t : Spec (.of K) ⟶ W) (f₁ f₂ : W ⟶ X) (ht : t ≫ f₁ = t ≫ f₂) {p : X}
    (h₁ : f₁ (t (closedPoint K)) = p) (h₂ : f₂ (t (closedPoint K)) = p)
    (s : X.presheaf.stalk p) :
    (stalkHomOfEq f₁ _ h₁).hom s - (stalkHomOfEq f₂ _ h₂).hom s ∈
      maximalIdeal (W.presheaf.stalk (t (closedPoint K))) := by
  have hker : ∀ x, (Scheme.stalkClosedPointTo t).hom x = 0 → x ∈ maximalIdeal _ := by
    intro x hx
    by_contra hnot
    have hu := ((IsLocalRing.mem_maximalIdeal x).not.mp hnot)
    rw [mem_nonunits_iff, not_not] at hu
    have := hu.map (Scheme.stalkClosedPointTo t).hom
    rw [hx] at this
    exact not_isUnit_zero this
  apply hker
  rw [map_sub, stalkClosedPointTo_stalkHomOfEq, stalkClosedPointTo_stalkHomOfEq, sub_eq_zero]
  exact stalkClosedPointTo_congr ht h₁ h₂ s

/-- A morphism `f` with a section `t` of the canonical point `Spec κ(p) ⟶ X` through `w`
induces an isomorphism of residue fields at `w`. -/
private lemma isIso_residueFieldMap_of_comp_eq {W X : Scheme.{u}} (f : W ⟶ X) {p : X}
    (t : Spec (.of (X.residueField p)) ⟶ W) (ht : t ≫ f = X.fromSpecResidueField p) :
    IsIso (f.residueFieldMap (t (closedPoint (X.residueField p)))) := by
  have e2 : (Scheme.SpecToEquivOfField (X.residueField p) X).symm ⟨p, 𝟙 _⟩ =
      X.fromSpecResidueField p := by
    change Spec.map (𝟙 _) ≫ X.fromSpecResidueField p = _
    rw [Spec.map_id]
    exact Category.id_comp _
  have h1 := congrArg (Scheme.SpecToEquivOfField (X.residueField p) X) ht
  rw [← e2, Equiv.apply_symm_apply] at h1
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp h1
  have he' : f.residueFieldMap (t (closedPoint (X.residueField p))) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo t) = (X.residueFieldCongr e).hom := by
    have := Scheme.descResidueField_stalkClosedPointTo_comp f t
    rw [← this]
    simp only [Category.comp_id] at he
    exact he
  set β := Scheme.descResidueField (Scheme.stalkClosedPointTo t)
  have hβ : Function.Injective β.hom := β.hom.injective
  have hc : Function.Bijective
      (f.residueFieldMap (t (closedPoint (X.residueField p))) ≫ β).hom := by
    rw [he']; exact (X.residueFieldCongr e).commRingCatIsoToRingEquiv.bijective
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap _).hom.injective, fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hc.2 (β.hom y)
  exact ⟨x, hβ hx⟩

/-- A point through which the canonical point `Spec κ(p) ⟶ X` of a closed point lifts is closed,
over a field. -/
private lemma isClosed_singleton_of_comp_eq {k : Type u} [Field k] {W X : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) [LocallyOfFiniteType sW] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (f : W ⟶ X) (hf : f ≫ sX = sW) {p : X}
    (hp : IsClosed ({p} : Set X)) (t : Spec (.of (X.residueField p)) ⟶ W)
    (ht : t ≫ f = X.fromSpecResidueField p) :
    IsClosed ({t (closedPoint (X.residueField p))} : Set W) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
  have : LocallyOfFiniteType (X.fromSpecResidueField p) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hp
  have : LocallyOfFiniteType (t ≫ sW) := by
    rw [← hf, ← Category.assoc, ht]; infer_instance
  have : LocallyOfFiniteType t := locallyOfFiniteType_of_comp t sW
  exact t.closePoints_subset_preimage_closedPoints
    (IsLocalRing.isClosed_singleton_closedPoint _)

/-- A section over `V` vanishing at a point vanishes after pulling back to `Spec K`. -/
private lemma appTop_topIso_inv_eq_zero {K : Type u} [Field K] {X : Scheme.{u}} {V : X.Opens}
    (g : Spec (.of K) ⟶ V.toScheme) (z : Γ(X, V)) {p : X} (hgp : V.ι (g (closedPoint K)) = p)
    (hpV : p ∈ V) (hz : (X.presheaf.germ V p hpV).hom z ∈ maximalIdeal (X.presheaf.stalk p)) :
    g.appTop.hom (V.topIso.inv.hom z) = 0 := by
  subst hgp
  have hinj : ∀ x : Spec (.of K), Function.Injective ((Spec (.of K)).Γevaluation x).hom := by
    intro x a b hab
    obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective a
    obtain ⟨b, rfl⟩ := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective b
    have := (((Scheme.ΓSpecIso (.of K)).inv ≫
      (Spec (.of K)).Γevaluation x).hom).injective
    exact congrArg _ (this hab)
  apply hinj (closedPoint K)
  have hnat := Scheme.Γevaluation_naturality_apply g (closedPoint K) (V.topIso.inv.hom z)
  have hm : (V.toScheme.presheaf.germ ⊤ (g (closedPoint K)) trivial).hom
      (V.topIso.inv.hom z) ∈ maximalIdeal _ := by
    rw [← germ_topIso_inv _ hpV]
    by_contra hnot
    have hu := ((IsLocalRing.mem_maximalIdeal _).not.mp hnot)
    rw [mem_nonunits_iff, not_not] at hu
    exact ((IsLocalRing.mem_maximalIdeal _).mp hz) (isUnit_of_map_unit _ _ hu)
  have : (V.toScheme.Γevaluation (g (closedPoint K))).hom (V.topIso.inv.hom z) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hm
  rw [map_zero, ← hnat, this, map_zero]

/-- Derivatives commute with pull-back along a smooth morphism. -/
private theorem comap_higherDerivativeIdeal {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [Smooth sY] (f : Y' ⟶ Y) [Smooth f] (sY' : Y' ⟶ Spec (.of k))
    (hf : f ≫ sY = sY') (hdim : ∀ C ∈ irreducibleComponents Y, 0 < topologicalKrullDim C)
    (K : Y.IdealSheafData) (n : ℕ) :
    (higherDerivativeIdeal sY K n).comap f = higherDerivativeIdeal sY' (K.comap f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ← ih,
      derivativeIdeal_comap_of_smooth sY sY' f hf hdim]

/-- The canonical point `Spec κ(p) ⟶ X` lifts to the fibre product of the maps `V ⟶ 𝔸_k` given
by two families of sections over `V` vanishing at `p`. -/
private lemma exists_lift_fromSpecResidueField_pullback {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {V : X.Opens} {p : X} (hpV : p ∈ V) {ι : Type u}
    (f f' : ι → Γ(X, V))
    (hf : ∀ i, (X.presheaf.germ V p hpV).hom (f i) ∈ maximalIdeal (X.presheaf.stalk p))
    (hf' : ∀ i, (X.presheaf.germ V p hpV).hom (f' i) ∈ maximalIdeal (X.presheaf.stalk p)) :
    ∃ t : Spec (.of (X.residueField p)) ⟶
        pullback (AffineSpace.homOfVector (V.ι ≫ sX) fun i ↦ V.topIso.inv (f i))
          (AffineSpace.homOfVector (V.ι ≫ sX) fun i ↦ V.topIso.inv (f' i)),
      t ≫ pullback.fst _ _ ≫ V.ι = X.fromSpecResidueField p ∧
        t ≫ pullback.snd _ _ ≫ V.ι = X.fromSpecResidueField p := by
  have hpr : Set.range (X.fromSpecResidueField p) ⊆ Set.range V.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    simpa using hpV
  let g : Spec (.of (X.residueField p)) ⟶ V.toScheme := IsOpenImmersion.lift V.ι _ hpr
  have hg : g ≫ V.ι = X.fromSpecResidueField p := IsOpenImmersion.lift_fac _ _ _
  have hgp : V.ι (g (closedPoint (X.residueField p))) = p :=
    (congrArg (fun F ↦ F (closedPoint (X.residueField p))) hg).trans
      (Scheme.fromSpecResidueField_apply p _)
  have hga : g ≫ AffineSpace.homOfVector (V.ι ≫ sX) (fun i ↦ V.topIso.inv (f i)) =
      g ≫ AffineSpace.homOfVector (V.ι ≫ sX) (fun i ↦ V.topIso.inv (f' i)) := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
        AffineSpace.homOfVector_appTop_coord]
      rw [appTop_topIso_inv_eq_zero g _ hgp hpV (hf i),
        appTop_topIso_inv_eq_zero g _ hgp hpV (hf' i)]
  exact ⟨pullback.lift g g hga, by simp only [pullback.lift_fst_assoc, hg],
    by simp only [pullback.lift_snd_assoc, hg]⟩

/-- Two étale morphisms over `k` with a common lift `t` through `w` of the canonical point
`Spec κ(p) ⟶ X` identify the completed local rings at `p` and at `w` in two ways `e₁, e₂`, which
differ by a `k`-automorphism `σ` of the completed local ring at `p` congruent to the identity
modulo the maximal ideal. -/
private lemma exists_completion_algEquiv {k : Type u} [Field k] {W X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f₁ f₂ : W ⟶ X) [Etale f₁] [Etale f₂] (hf : f₁ ≫ sX = f₂ ≫ sX)
    {p : X} (t : Spec (.of (X.residueField p)) ⟶ W) (ht₁ : t ≫ f₁ = X.fromSpecResidueField p)
    (ht₂ : t ≫ f₂ = X.fromSpecResidueField p) {w : W} (hw : t (closedPoint _) = w)
    (h₁ : f₁ w = p) (h₂ : f₂ w = p) :
    letI := completedAlgebra sX p
    ∃ (e₁ e₂ : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃+*
        AdicCompletion (maximalIdeal (W.presheaf.stalk w)) (W.presheaf.stalk w))
      (σ : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃ₐ[k]
        AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)),
      e₁.toRingHom.comp (algebraMap _ _) = (algebraMap _ _).comp (stalkHomOfEq f₁ w h₁).hom ∧
      e₂.toRingHom.comp (algebraMap _ _) = (algebraMap _ _).comp (stalkHomOfEq f₂ w h₂).hom ∧
      (∀ x, e₁ (σ x) = e₂ x) ∧
      ∀ s, algebraMap (X.presheaf.stalk p) (AdicCompletion (maximalIdeal
        (X.presheaf.stalk p)) (X.presheaf.stalk p)) s - σ (algebraMap _ _ s) ∈
        (maximalIdeal (X.presheaf.stalk p)).map
          (algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk p))
            (X.presheaf.stalk p))) := by
  letI := completedAlgebra sX p
  subst hw
  have := isIso_residueFieldMap_of_comp_eq f₁ t ht₁
  have := isIso_residueFieldMap_of_comp_eq f₂ t ht₂
  obtain ⟨e₁, he₁, hm₁⟩ := exists_completion_ringEquiv f₁ _ h₁
  obtain ⟨e₂, he₂, -⟩ := exists_completion_ringEquiv f₂ _ h₂
  have hφ₁ : ∀ a, e₁ (algebraMap _ _ a) = algebraMap _ _ ((stalkHomOfEq f₁ _ h₁).hom a) :=
    fun a ↦ RingHom.congr_fun he₁ a
  have hφ₂ : ∀ a, e₂ (algebraMap _ _ a) = algebraMap _ _ ((stalkHomOfEq f₂ _ h₂).hom a) :=
    fun a ↦ RingHom.congr_fun he₂ a
  have hk : ∀ c : k, e₁ (algebraMap _ _ (@algebraMap k _ _ _ (MMP.Mori.stalkAlgebra sX p) c)) =
      e₂ (algebraMap _ _ (@algebraMap k _ _ _ (MMP.Mori.stalkAlgebra sX p) c)) := fun c ↦ by
    rw [hφ₁, hφ₂, stalkHomOfEq_algebraMap, stalkHomOfEq_algebraMap, hf]
  let σ : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃ₐ[k]
      AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) :=
    AlgEquiv.ofRingEquiv (f := e₂.trans e₁.symm) (fun c ↦ by
      change e₁.symm (e₂ (algebraMap _ _ (@algebraMap k _ _ _ (MMP.Mori.stalkAlgebra sX p) c))) =
        algebraMap _ _ (@algebraMap k _ _ _ (MMP.Mori.stalkAlgebra sX p) c)
      rw [RingEquiv.symm_apply_eq]
      exact (hk c).symm)
  have hσ : ∀ x, e₁ (σ x) = e₂ x := fun x ↦ by
    change e₁ (e₁.symm (e₂ x)) = e₂ x
    exact e₁.apply_symm_apply _
  refine ⟨e₁, e₂, σ, he₁, he₂, hσ, fun s ↦ ?_⟩
  rw [← Ideal.comap_map_of_bijective e₁.toRingHom e₁.bijective (I := Ideal.map _ _),
    Ideal.mem_comap, hm₁]
  change e₁ (algebraMap _ _ s - σ (algebraMap _ _ s)) ∈ _
  rw [map_sub, hσ, hφ₁, hφ₂, ← map_sub]
  exact Ideal.mem_map_of_mem _
    (sub_mem_maximalIdeal_of_comp_eq t f₁ f₂ (ht₁.trans ht₂.symm) h₁ h₂ s)

/-- Equality of stalks of two ideal sheaves on a locally Noetherian scheme spreads out to a
neighbourhood. -/
private lemma setOf_stalk_eq_mem_nhds {X : Scheme.{u}} [IsLocallyNoetherian X]
    {A B : X.IdealSheafData} {x : X} (h : IdealSheafData.stalk A x = IdealSheafData.stalk B x) :
    {y | IdealSheafData.stalk A y = IdealSheafData.stalk B y} ∈ nhds x := by
  obtain ⟨U₁, hxU₁, hU₁⟩ := exists_open_stalk_le A B x h.le
  obtain ⟨U₂, hxU₂, hU₂⟩ := exists_open_stalk_le B A x h.ge
  exact Filter.mem_of_superset
    (Filter.inter_mem (U₁.isOpen.mem_nhds hxU₁) (U₂.isOpen.mem_nhds hxU₂))
    (fun y hy ↦ le_antisymm (hU₁ y hy.1) (hU₂ y hy.2))

/-- Two morphisms to an affine scheme agree on the closed subscheme of `D(s₀) ⊆ W₀` cut out by
`A` if `s₀` times the differences of the pull-backs of global sections lie in `A` over the affine
open `W₀`. -/
private lemma subschemeι_comp_eq_of_mul_sub_mem {W Y : Scheme.{u}} [IsAffine Y] (f g : W ⟶ Y)
    (A : W.IdealSheafData) {W₀ : W.Opens} (hW₀ : IsAffineOpen W₀) (s₀ : Γ(W, W₀))
    (hs₀ : ∀ h' : Γ(Y, ⊤), s₀ * (W.presheaf.map (homOfLE (le_top : W₀ ≤ ⊤)).op).hom
      (f.appTop.hom h' - g.appTop.hom h') ∈ A.ideal ⟨W₀, hW₀⟩) :
    (A.comap (W.basicOpen s₀).ι).subschemeι ≫ (W.basicOpen s₀).ι ≫ f =
      (A.comap (W.basicOpen s₀).ι).subschemeι ≫ (W.basicOpen s₀).ι ≫ g := by
  set U : W.Opens := W.basicOpen s₀
  have : IsAffine U.toScheme := hW₀.basicOpen s₀
  have hUW₀ : U ≤ W₀ := W.basicOpen_le s₀
  apply ext_of_isAffine
  ext h'
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  have hU'W₀ : U.ι ''ᵁ ⊤ ≤ W₀ := by rwa [Scheme.Opens.ι_image_top]
  have hU'U : U.ι ''ᵁ ⊤ ≤ U := by rw [Scheme.Opens.ι_image_top]
  have hunit : IsUnit ((W.presheaf.map (homOfLE hU'W₀).op).hom s₀) := by
    have h2 := (RingedSpace.isUnit_res_basicOpen W.toRingedSpace s₀).map
      (W.presheaf.map (homOfLE hU'U).op).hom
    have h3 : W.presheaf.map (homOfLE hU'W₀).op =
        W.presheaf.map (homOfLE (W.basicOpen_le s₀)).op ≫ W.presheaf.map (homOfLE hU'U).op := by
      rw [← Functor.map_comp]; rfl
    rw [h3, CommRingCat.comp_apply]
    exact h2
  have hmem : (U.ι.appTop).hom (f.appTop.hom h' - g.appTop.hom h') ∈
      (A.comap U.ι).ideal ⟨⊤, isAffineOpen_top _⟩ := by
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Ideal.mem_comap,
      Scheme.Opens.ι_appIso]
    change (W.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op).hom
      (f.appTop.hom h' - g.appTop.hom h') ∈ _
    have hU'aff : IsAffineOpen (U.ι ''ᵁ ⊤) :=
      (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι
    suffices key : (W.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op).hom
        (f.appTop.hom h' - g.appTop.hom h') ∈ A.ideal ⟨U.ι ''ᵁ ⊤, hU'aff⟩ from key
    rw [← A.map_ideal (U := ⟨U.ι ''ᵁ ⊤, hU'aff⟩) (V := ⟨W₀, hW₀⟩) hU'W₀]
    have hres : (W.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op).hom
        (f.appTop.hom h' - g.appTop.hom h') =
        (W.presheaf.map (homOfLE hU'W₀).op).hom ((W.presheaf.map
          (homOfLE (le_top : W₀ ≤ ⊤)).op).hom (f.appTop.hom h' - g.appTop.hom h')) := by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [hres, ← Ideal.unit_mul_mem_iff_mem _ hunit, ← map_mul]
    exact Ideal.mem_map_of_mem _ (hs₀ h')
  rwa [← Scheme.IdealSheafData.ker_subschemeι_app (A.comap U.ι) ⟨⊤, isAffineOpen_top _⟩] at hmem

/-- If the differences of the pull-backs of global sections along `f, g : W ⟶ Y` lie in the stalk
of `A` at `w`, then `f` and `g` agree on the closed subscheme cut out by `A` over an open
neighbourhood of `w` inside any given neighbourhood `S`. -/
private lemma exists_open_subschemeι_comp_eq {W Y : Scheme.{u}} [IsLocallyNoetherian W]
    [IsAffine Y] (f g : W ⟶ Y) (A : W.IdealSheafData) {w : W} {S : Set W} (hS : S ∈ nhds w)
    (hδ : ∀ h' : Γ(Y, ⊤), (W.presheaf.germ ⊤ w trivial).hom (f.appTop.hom h' - g.appTop.hom h')
      ∈ IdealSheafData.stalk A w) :
    ∃ U : W.Opens, w ∈ U ∧ (∀ u : U.toScheme, U.ι u ∈ S) ∧
      (A.comap U.ι).subschemeι ≫ U.ι ≫ f = (A.comap U.ι).subschemeι ≫ U.ι ≫ g := by
  obtain ⟨T, hTS, hTo, hwT⟩ := mem_nhds_iff.mp hS
  obtain ⟨W₀, hW₀, hwW₀, hW₀T⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨T, hTo⟩) hwT
  let J₀ : Ideal Γ(W, W₀) := Ideal.span (Set.range fun h' : Γ(Y, ⊤) ↦
    (W.presheaf.map (homOfLE (le_top : W₀ ≤ ⊤)).op).hom (f.appTop.hom h' - g.appTop.hom h'))
  have hJ₀ : J₀.map (W.presheaf.germ W₀ w hwW₀).hom ≤ IdealSheafData.stalk A w := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨h', rfl⟩, rfl⟩
    rw [TopCat.Presheaf.germ_res_apply]
    exact hδ h'
  obtain ⟨s₀, hws₀, hs₀⟩ := exists_basicOpen_mul_mem A hW₀ hwW₀ J₀ hJ₀
  exact ⟨W.basicOpen s₀, hws₀, fun u ↦ hTS (hW₀T (W.basicOpen_le s₀ u.2)),
    subschemeι_comp_eq_of_mul_sub_mem f g A hW₀ s₀ fun h' ↦ hs₀ _ (Ideal.subset_span ⟨h', rfl⟩)⟩

/-- `exists_etale_realization_of_formalUniqueness` with the compatibility `hcomp` (always true)
as a hypothesis of the last clause instead of an existential witness: there are a closed point
`w ∈ W` over `p` under both `ψ` and `ψ'` and an open neighbourhood `U` of `w` on which `ψ, ψ'`
are étale, pull back `H, H'` to the same ideal and each of `I` and `E_i` to the same ideal, and
pull the diagonal ideal of `X ×_k X` back into `D^{m-1}` of the pull-back of `I`. -/
private theorem exists_etale_realization_core {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsMCInvariant sX I) (hIgen : IsNonzeroAtGenericPoints I)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : maxOrder I = m)
    {E : OrderedDivisor X} (hEo : E.IsOrderedDivisor) (hE : E.IsSNC sX)
    {H H' : X.IdealSheafData} (hH : IsSmoothHypersurface sX H) (hH' : IsSmoothHypersurface sX H')
    (hHI : H ≤ maximalContactIdeal sX I) (hH'I : H' ≤ maximalContactIdeal sX I)
    {p : X} (hp : IsClosed ({p} : Set X)) (hpm : multAt I p = m)
    {V : X.Opens} (hV : IsAffineOpen V) (hpV : p ∈ V)
    {n : ℕ} {x₁ x₁' : Γ(X, V)} {y : Fin n → Γ(X, V)}
    (hloc : IsLocalCoordinatesAt sX V (Fin.cons x₁ y : Fin (n + 1) → _) p hpV)
    (hloc' : IsLocalCoordinatesAt sX V (Fin.cons x₁' y : Fin (n + 1) → _) p hpV)
    (hx₁ : IdealSheafData.stalk H p = Ideal.span {(X.presheaf.germ V p hpV).hom x₁})
    (hx₁' : IdealSheafData.stalk H' p = Ideal.span {(X.presheaf.germ V p hpV).hom x₁'})
    (hreg : MMP.Mori.IsRegularSystemOfParameters
      (fun i ↦ (X.presheaf.germ V p hpV).hom ((Fin.cons x₁ y : Fin (n + 1) → _) i)))
    (hreg' : MMP.Mori.IsRegularSystemOfParameters
      (fun i ↦ (X.presheaf.germ V p hpV).hom ((Fin.cons x₁' y : Fin (n + 1) → _) i)))
    (hEy : ∀ i, p ∈ (E.E i).support →
      ∃ l, IdealSheafData.stalk (E.E i) p = Ideal.span {(X.presheaf.germ V p hpV).hom (y l)}) :
    let a := AffineSpace.homOfVector (V.ι ≫ sX)
      (fun i : ULift.{u} (Fin (n + 1)) ↦
        V.topIso.inv ((Fin.cons x₁ y : Fin (n + 1) → _) i.down))
    let a' := AffineSpace.homOfVector (V.ι ≫ sX)
      (fun i : ULift.{u} (Fin (n + 1)) ↦
        V.topIso.inv ((Fin.cons x₁' y : Fin (n + 1) → _) i.down))
    let W : Scheme.{u} := pullback a a'
    let ψ : W ⟶ X := pullback.fst a a' ≫ V.ι
    let ψ' : W ⟶ X := pullback.snd a a' ≫ V.ι
    ∃ (U : W.Opens) (w : W) (_ : w ∈ U),
      IsClosed ({w} : Set W) ∧ ψ w = p ∧ ψ' w = p ∧
      Etale (U.ι ≫ ψ) ∧ Etale (U.ι ≫ ψ') ∧
      H.comap (U.ι ≫ ψ) = H'.comap (U.ι ≫ ψ') ∧
      I.comap (U.ι ≫ ψ) = I.comap (U.ι ≫ ψ') ∧
      (∀ i, (E.E i).comap (U.ι ≫ ψ) = (E.E i).comap (U.ι ≫ ψ')) ∧
      ∀ hcomp : (U.ι ≫ ψ) ≫ sX = (U.ι ≫ ψ') ≫ sX,
      (pullback.diagonal sX).ker.comap (pullback.lift (U.ι ≫ ψ) (U.ι ≫ ψ') hcomp) ≤
        higherDerivativeIdeal ((U.ι ≫ ψ) ≫ sX) (I.comap (U.ι ≫ ψ)) ((maxOrder I).toNat - 1) := by
  intro a a' W ψ ψ'
  have ha : Etale a := etale_homOfVector_of_isLocalCoordinatesOn sX hV hloc.1
  have ha' : Etale a' := etale_homOfVector_of_isLocalCoordinatesOn sX hV hloc'.1
  have hψ : Etale ψ := by dsimp only [ψ]; infer_instance
  have hψ' : Etale ψ' := by dsimp only [ψ']; infer_instance
  have hcompW : ψ ≫ sX = ψ' ≫ sX := by
    simpa only [ψ, ψ', Category.assoc] using fst_comp_eq_snd_comp (V.ι ≫ sX) _ _
  have hcoord : ∀ i : ULift.{u} (Fin (n + 1)),
      (pullback.fst a a').appTop.hom (V.topIso.inv.hom ((Fin.cons x₁ y : Fin (n + 1) → _) i.down))
        = (pullback.snd a a').appTop.hom
          (V.topIso.inv.hom ((Fin.cons x₁' y : Fin (n + 1) → _) i.down)) := by
    intro i
    have h := congrArg (fun F ↦ F.appTop.hom (AffineSpace.coord (Spec (.of k)) i))
      (pullback.condition (f := a) (g := a'))
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, a, a',
      AffineSpace.homOfVector_appTop_coord] using h
  obtain ⟨t, htψ, htψ'⟩ : ∃ t : Spec (.of (X.residueField p)) ⟶ W,
      t ≫ ψ = X.fromSpecResidueField p ∧ t ≫ ψ' = X.fromSpecResidueField p :=
    exists_lift_fromSpecResidueField_pullback sX hpV
      (fun i : ULift.{u} (Fin (n + 1)) ↦ (Fin.cons x₁ y : Fin (n + 1) → _) i.down)
      (fun i ↦ (Fin.cons x₁' y : Fin (n + 1) → _) i.down) (fun i ↦ hloc.2 i.down)
      fun i ↦ hloc'.2 i.down
  let w : W := t (closedPoint (X.residueField p))
  have hψw : ψ w = p :=
    (congrArg (fun F ↦ F (closedPoint (X.residueField p))) htψ).trans
      (Scheme.fromSpecResidueField_apply p _)
  have hψ'w : ψ' w = p :=
    (congrArg (fun F ↦ F (closedPoint (X.residueField p))) htψ').trans
      (Scheme.fromSpecResidueField_apply p _)
  have hwc : IsClosed ({w} : Set W) := isClosed_singleton_of_comp_eq (ψ ≫ sX) sX ψ rfl hp t htψ
  let := completedAlgebra sX p
  obtain ⟨e₁, e₂, σ, he₁, he₂, hσ, hσ3⟩ :=
    exists_completion_algEquiv sX ψ ψ' hcompW t htψ htψ' rfl hψw hψ'w
  have hφ₁ : ∀ a, e₁ (algebraMap _ _ a) = algebraMap _ _ ((stalkHomOfEq ψ w hψw).hom a) :=
    fun a ↦ RingHom.congr_fun he₁ a
  have hφ₂ : ∀ a, e₂ (algebraMap _ _ a) = algebraMap _ _ ((stalkHomOfEq ψ' w hψ'w).hom a) :=
    fun a ↦ RingHom.congr_fun he₂ a
  have hgerm₁ : ∀ z : Γ(X, V), e₁ (algebraMap _ _ ((X.presheaf.germ V p hpV).hom z)) =
      algebraMap _ _ ((W.presheaf.germ ⊤ w trivial).hom
        ((pullback.fst a a').appTop.hom (V.topIso.inv.hom z))) := fun z ↦ by
    rw [hφ₁]
    exact congrArg _ (stalkHomOfEq_germ (pullback.fst a a') w hψw hpV z)
  have hgerm₂ : ∀ z : Γ(X, V), e₂ (algebraMap _ _ ((X.presheaf.germ V p hpV).hom z)) =
      algebraMap _ _ ((W.presheaf.germ ⊤ w trivial).hom
        ((pullback.snd a a').appTop.hom (V.topIso.inv.hom z))) := fun z ↦ by
    rw [hφ₂]
    exact congrArg _ (stalkHomOfEq_germ (pullback.snd a a') w hψ'w hpV z)
  have hσc : ∀ i, σ (algebraMap _ _ ((X.presheaf.germ V p hpV).hom
      ((Fin.cons x₁' y : Fin (n + 1) → _) i))) =
      algebraMap _ _ ((X.presheaf.germ V p hpV).hom ((Fin.cons x₁ y : Fin (n + 1) → _) i)) :=
    fun i ↦ e₁.injective <| by rw [hσ, hgerm₂, hgerm₁, hcoord ⟨i⟩]
  obtain ⟨hF1, hF2, hF3, hF4⟩ := (formalUniqueness_of_le_maximalContactIdeal sX hX hdim hI hIgen
    hm1 hm hEo hE hH hH' hHI hH'I hp hpm hx₁ hx₁' (Fin.comp_cons _ _ _ ▸ hreg)
    (Fin.comp_cons _ _ _ ▸ hreg') hEy).2 σ (by simpa only [Fin.cons_zero] using hσc 0)
    (fun l ↦ by simpa only [Fin.cons_succ] using hσc l.succ) hσ3
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (ψ ≫ sX)
  have he₂σ : e₂.toRingHom = e₁.toRingHom.comp (σ : _ →+* _) :=
    RingHom.ext fun x ↦ (hσ x).symm
  have hstalk : ∀ J J' : X.IdealSheafData, (completedIdeal J' p).map σ = completedIdeal J p →
      IdealSheafData.stalk (J.comap ψ) w = IdealSheafData.stalk (J'.comap ψ') w :=
    fun J J' hJ ↦ stalk_comap_eq_of_map_completedIdeal_eq ψ ψ' hψw hψ'w J J' e₁ e₂ he₁ he₂ <| by
      rw [he₂σ, ← Ideal.map_map, Ideal.map_coe, hJ]
  have hS : {y | IdealSheafData.stalk (H.comap ψ) y = IdealSheafData.stalk (H'.comap ψ') y} ∩
      {y | IdealSheafData.stalk (I.comap ψ) y = IdealSheafData.stalk (I.comap ψ') y} ∩
      ⋂ i, {y | IdealSheafData.stalk ((E.E i).comap ψ) y =
        IdealSheafData.stalk ((E.E i).comap ψ') y} ∈ nhds w :=
    Filter.inter_mem (Filter.inter_mem (setOf_stalk_eq_mem_nhds (hstalk _ _ hF1))
      (setOf_stalk_eq_mem_nhds (hstalk _ _ hF2)))
      (Filter.iInter_mem.mpr fun i ↦ setOf_stalk_eq_mem_nhds (hstalk _ _ (hF3 i)))
  let A : W.IdealSheafData := (higherDerivativeIdeal sX I ((maxOrder I).toNat - 1)).comap ψ
  let δ : Γ(V.toScheme, ⊤) → Γ(W, ⊤) := fun h' ↦
    (pullback.fst a a').appTop.hom h' - (pullback.snd a a').appTop.hom h'
  have hδw : ∀ h', (W.presheaf.germ ⊤ w trivial).hom (δ h') ∈ IdealSheafData.stalk A w := by
    intro h'
    obtain ⟨z, rfl⟩ : ∃ z, V.topIso.inv.hom z = h' :=
      ⟨V.topIso.hom.hom h', by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl⟩
    rw [← comap_map_adicCompletion (IdealSheafData.stalk A w), Ideal.mem_comap]
    change _ ∈ completedIdeal A w
    rw [completedIdeal_comap ψ w hψw _ e₁ he₁]
    have hMC := (completedIdeal_higherDerivativeIdeal sX hX hdim hp I).2
      (by rw [hm]; exact_mod_cast hm1)
    simp only [maximalContactIdeal] at hMC
    rw [hMC]
    simp only [δ, map_sub]
    rw [← hgerm₁ z, ← (hσ _).trans (hgerm₂ z), ← map_sub]
    exact Ideal.mem_map_of_mem _ (hF4 _)
  have : IsAffine V.toScheme := hV
  obtain ⟨U, hwU, hUS, hfs⟩ :=
    exists_open_subschemeι_comp_eq (pullback.fst a a') (pullback.snd a a') A hS hδw
  refine ⟨U, w, hwU, hwc, hψw, hψ'w, inferInstance, inferInstance, ?_, ?_, ?_, fun hcomp ↦ ?_⟩
  · exact comap_comp_eq_of_stalk_eq ψ ψ' H H' U fun u ↦ (hUS u).1.1
  · exact comap_comp_eq_of_stalk_eq ψ ψ' I I U fun u ↦ (hUS u).1.2
  · exact fun i ↦ comap_comp_eq_of_stalk_eq ψ ψ' _ _ U fun u ↦ Set.mem_iInter.mp (hUS u).2 i
  rw [← comap_higherDerivativeIdeal sX (U.ι ≫ ψ) _ rfl hdim I,
    Scheme.IdealSheafData.comap_comp _ U.ι ψ]
  apply ker_diagonal_comap_le_of_eq
  change (A.comap U.ι).subschemeι ≫ U.ι ≫ pullback.fst a a' ≫ V.ι =
    (A.comap U.ι).subschemeι ≫ U.ι ≫ pullback.snd a a' ≫ V.ι
  simpa only [Category.assoc] using congrArg (· ≫ V.ι) hfs

/-- **Étale realization of formal equivalence** (Kollár 3.95, étale part). In the setting of
`formalUniqueness_of_le_maximalContactIdeal`, let `V` be an affine
open neighbourhood of `p` and `x₁, x₁', y_l ∈ 𝒪_X(V)` such that `(x₁, y)` and `(x₁', y)` are local
coordinates at `p`. Let `a, a' : V → 𝔸ⁿ⁺¹_k` be the corresponding maps, `W = V ×_{a, a'} V` and
`ψ, ψ' : W → X` the two projections. Then there are an open `U ⊆ W` and a closed point `w ∈ U`
with `ψ w = ψ' w = p` such that `ψ|_U, ψ'|_U` are étale, `ψ|_U⁻¹ H = ψ'|_U⁻¹ H'`,
`ψ|_U^* I = ψ'|_U^* I`, `ψ|_U⁻¹ E^i = ψ'|_U⁻¹ E^i` for all `i`, and the pull-back of the ideal of
the diagonal of `X ×_k X` along `(ψ|_U, ψ'|_U)` lies in `D^{m-1}(ψ|_U^* I)`. -/
@[mmp "lem_kr3d_etale_realization_of_formal_equivalence"]
public theorem exists_etale_realization_of_formalUniqueness {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsMCInvariant sX I) (hIgen : IsNonzeroAtGenericPoints I)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : maxOrder I = m)
    {E : OrderedDivisor X} (hEo : E.IsOrderedDivisor) (hE : E.IsSNC sX)
    {H H' : X.IdealSheafData} (hH : IsSmoothHypersurface sX H) (hH' : IsSmoothHypersurface sX H')
    (hHI : H ≤ maximalContactIdeal sX I) (hH'I : H' ≤ maximalContactIdeal sX I)
    {p : X} (hp : IsClosed ({p} : Set X)) (hpm : multAt I p = m)
    {V : X.Opens} (hV : IsAffineOpen V) (hpV : p ∈ V)
    {n : ℕ} {x₁ x₁' : Γ(X, V)} {y : Fin n → Γ(X, V)}
    (hloc : IsLocalCoordinatesAt sX V (Fin.cons x₁ y : Fin (n + 1) → _) p hpV)
    (hloc' : IsLocalCoordinatesAt sX V (Fin.cons x₁' y : Fin (n + 1) → _) p hpV)
    (hx₁ : IdealSheafData.stalk H p = Ideal.span {(X.presheaf.germ V p hpV).hom x₁})
    (hx₁' : IdealSheafData.stalk H' p = Ideal.span {(X.presheaf.germ V p hpV).hom x₁'})
    (hreg : MMP.Mori.IsRegularSystemOfParameters
      (fun i ↦ (X.presheaf.germ V p hpV).hom ((Fin.cons x₁ y : Fin (n + 1) → _) i)))
    (hreg' : MMP.Mori.IsRegularSystemOfParameters
      (fun i ↦ (X.presheaf.germ V p hpV).hom ((Fin.cons x₁' y : Fin (n + 1) → _) i)))
    (hEy : ∀ i, p ∈ (E.E i).support →
      ∃ l, IdealSheafData.stalk (E.E i) p = Ideal.span {(X.presheaf.germ V p hpV).hom (y l)}) :
    let a := AffineSpace.homOfVector (V.ι ≫ sX)
      (fun i : ULift.{u} (Fin (n + 1)) ↦
        V.topIso.inv ((Fin.cons x₁ y : Fin (n + 1) → _) i.down))
    let a' := AffineSpace.homOfVector (V.ι ≫ sX)
      (fun i : ULift.{u} (Fin (n + 1)) ↦
        V.topIso.inv ((Fin.cons x₁' y : Fin (n + 1) → _) i.down))
    let W : Scheme.{u} := pullback a a'
    let ψ : W ⟶ X := pullback.fst a a' ≫ V.ι
    let ψ' : W ⟶ X := pullback.snd a a' ≫ V.ι
    ∃ (U : W.Opens) (w : W) (hw : w ∈ U) (hcomp : (U.ι ≫ ψ) ≫ sX = (U.ι ≫ ψ') ≫ sX),
      IsClosed ({w} : Set W) ∧ ψ w = p ∧ ψ' w = p ∧
      Etale (U.ι ≫ ψ) ∧ Etale (U.ι ≫ ψ') ∧
      H.comap (U.ι ≫ ψ) = H'.comap (U.ι ≫ ψ') ∧
      I.comap (U.ι ≫ ψ) = I.comap (U.ι ≫ ψ') ∧
      (∀ i, (E.E i).comap (U.ι ≫ ψ) = (E.E i).comap (U.ι ≫ ψ')) ∧
      (pullback.diagonal sX).ker.comap (pullback.lift (U.ι ≫ ψ) (U.ι ≫ ψ') hcomp) ≤
        higherDerivativeIdeal ((U.ι ≫ ψ) ≫ sX) (I.comap (U.ι ≫ ψ)) ((maxOrder I).toNat - 1) := by
  intro a a' W ψ ψ'
  obtain ⟨U, w, hw, hw1, hw2, hw3, h1, h2, h3, h4, h5, h6⟩ :=
    exists_etale_realization_core sX hX hdim hI hIgen hm1 hm hEo hE hH hH' hHI hH'I hp hpm hV hpV
      hloc hloc' hx₁ hx₁' hreg hreg' hEy
  have hcomp : (U.ι ≫ ψ) ≫ sX = (U.ι ≫ ψ') ≫ sX := by
    simpa only [ψ, ψ', Category.assoc] using U.ι ≫= fst_comp_eq_snd_comp (V.ι ≫ sX) _ _
  exact ⟨U, w, hw, hcomp, hw1, hw2, hw3, h1, h2, h3, h4, h5, h6 hcomp⟩

end EtaleRealization

/-! ### Logarithmic decomposition for one blow-up -/

section LogDecomposition

/-! ### Commutative algebra -/

section Ring

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

private def logSpanR (k : Type*) {A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (I K : Ideal A) : Ideal A :=
  Ideal.span {g | ∃ δ : Derivation k A A, (∀ s ∈ I, δ s ∈ I) ∧ ∃ f ∈ K, δ f = g}

private def pSpan (d : Derivation k A A) (K : Ideal A) : Ideal A := Ideal.span (d '' K)

private theorem mem_logSpanR {I K : Ideal A} {δ : Derivation k A A} (hδ : ∀ s ∈ I, δ s ∈ I) {f : A}
    (hf : f ∈ K) : δ f ∈ logSpanR k I K := Ideal.subset_span ⟨δ, hδ, f, hf, rfl⟩

private theorem mem_pSpan {d : Derivation k A A} {K : Ideal A} {f : A} (hf : f ∈ K) :
    d f ∈ pSpan d K :=
  Ideal.subset_span ⟨f, hf, rfl⟩

private theorem logSpanR_mono (I : Ideal A) : Monotone (logSpanR k I) := fun _ _ h =>
  Ideal.span_mono fun _ ⟨δ, hδ, f, hf, e⟩ => ⟨δ, hδ, f, h hf, e⟩

private theorem derivativeIdealOfRing_mono : Monotone (derivativeIdealOfRing k (R := A)) :=
  fun _ _ h => Ideal.span_mono fun _ ⟨δ, f, hf, e⟩ => ⟨δ, f, h hf, e⟩

private theorem pSpan_le_iff {d : Derivation k A A} {K M : Ideal A} :
    pSpan d K ≤ M ↔ ∀ f ∈ K, d f ∈ M := by
  rw [pSpan, Ideal.span_le]; exact Set.image_subset_iff

private theorem logSpanR_sup_le (I J K : Ideal A) :
    logSpanR k I (J ⊔ K) ≤ logSpanR k I J ⊔ logSpanR k I K := by
  rw [logSpanR, Ideal.span_le]
  rintro _ ⟨δ, hδ, f, hf, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
  rw [SetLike.mem_coe, map_add]
  exact add_mem (Ideal.mem_sup_left (mem_logSpanR hδ ha)) (Ideal.mem_sup_right (mem_logSpanR hδ hb))

/-- A derivation killing `t` preserves `(t)`. -/
private theorem preserves_of_apply_eq_zero {t : A} {δ : Derivation k A A} (h : δ t = 0) :
    ∀ s ∈ Ideal.span {t}, δ s ∈ Ideal.span {t} := by
  intro s hs
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hs
  rw [Derivation.leibniz, h, smul_zero, zero_add, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)

private theorem preserves_smul {t : A} (d : Derivation k A A) :
    ∀ s ∈ Ideal.span {t}, (t • d) s ∈ Ideal.span {t} := by
  intro s _
  rw [Derivation.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)

/-- With a derivation `d'` and `u` with `d' t = 0`, `d' u = 1`, every ideal lies in its
logarithmic derivative along `(t)`. -/
private theorem le_logSpanR {t u : A} {d' : Derivation k A A} (h2 : d' t = 0) (h3 : d' u = 1)
    (K : Ideal A) : K ≤ logSpanR k (Ideal.span {t}) K := by
  intro f hf
  have hlog := preserves_of_apply_eq_zero h2
  have e : f = d' (u * f) - u * d' f := by
    rw [Derivation.leibniz, h3, smul_eq_mul, smul_eq_mul]; ring
  rw [e]
  exact sub_mem (mem_logSpanR hlog (K.mul_mem_left u hf))
    (Ideal.mul_mem_left _ _ (mem_logSpanR hlog hf))

section

variable {t : A} {d : Derivation k A A} (h1 : d t = 1)

include h1

private theorem derivativeIdealOfRing_le (K : Ideal A) :
    derivativeIdealOfRing k K ≤ logSpanR k (Ideal.span {t}) K ⊔ pSpan d K := by
  rw [derivativeIdealOfRing, Ideal.span_le]
  rintro _ ⟨δ, f, hf, rfl⟩
  have hν : (δ - δ t • d) t = 0 := by simp [h1]
  have : δ f = (δ - δ t • d) f + δ t * d f := by simp
  rw [SetLike.mem_coe, this]
  exact add_mem (Ideal.mem_sup_left (mem_logSpanR (preserves_of_apply_eq_zero hν) hf))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (mem_pSpan hf)))

private theorem apply_logSpan_mem (K : Ideal A) {δ : Derivation k A A}
    (hδ : ∀ s ∈ Ideal.span {t}, δ s ∈ Ideal.span {t}) {f : A} (hf : f ∈ K) :
    d (δ f) ∈ logSpanR k (Ideal.span {t}) K ⊔ pSpan d K ⊔
      logSpanR k (Ideal.span {t}) (pSpan d K) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hδ t (Ideal.mem_span_singleton_self t))
  set μ : Derivation k A A := ⁅d, δ⁆
  have hμt : μ t = a + t * d a := by
    simp only [μ, Derivation.commutator_apply, h1, Derivation.map_one_eq_zero, sub_zero, ← ha,
      Derivation.leibniz, smul_eq_mul, mul_one]
  have hν : (μ - μ t • d) t = 0 := by simp [h1]
  have key : d (δ f) = δ (d f) + (a * d f + (d a) * (t • d) f) + (μ - μ t • d) f := by
    have : μ f = d (δ f) - δ (d f) := Derivation.commutator_apply f
    simp only [Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hμt]
    rw [this]; ring
  rw [key]
  refine add_mem (add_mem (Ideal.mem_sup_right (mem_logSpanR hδ (mem_pSpan hf))) ?_)
    (Ideal.mem_sup_left (Ideal.mem_sup_left
      (mem_logSpanR (preserves_of_apply_eq_zero hν) hf)))
  exact add_mem (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (mem_pSpan hf))))
    (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mul_mem_left _ _
      (mem_logSpanR (preserves_smul d) hf))))

private theorem pSpan_logSpanR_le (K : Ideal A) :
    pSpan d (logSpanR k (Ideal.span {t}) K) ≤ logSpanR k (Ideal.span {t}) K ⊔ pSpan d K ⊔
      logSpanR k (Ideal.span {t}) (pSpan d K) := by
  rw [pSpan_le_iff]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨δ, hδ, f, hf, rfl⟩ := hg
    exact apply_logSpan_mem h1 K hδ hf
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a ha ih =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ c ih)
      (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ ha)))

variable {u : A} {d' : Derivation k A A} (h2 : d' t = 0) (h3 : d' u = 1)

include h2 h3

/-- `∂ (L^a G_j) ⊆ L^a G_j + L^a G_{j+1}` from `∂ G_j ⊆ G_j + G_{j+1}`. -/
private theorem pSpan_iterate_le {G G' : Ideal A} (hG : pSpan d G ≤ G ⊔ G') (a : ℕ) :
    pSpan d ((logSpanR k (Ideal.span {t}))^[a] G) ≤
      (logSpanR k (Ideal.span {t}))^[a] G ⊔ (logSpanR k (Ideal.span {t}))^[a] G' := by
  set L := logSpanR k (A := A) (Ideal.span {t})
  induction a with
  | zero => exact hG
  | succ a ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine (pSpan_logSpanR_le h1 _).trans (sup_le (sup_le le_sup_left ?_) ?_)
    · exact ih.trans (sup_le_sup (le_logSpanR h2 h3 _) (le_logSpanR h2 h3 _))
    · exact (logSpanR_mono _ ih).trans (logSpanR_sup_le _ _ _)

/-- The ring form of the inclusion `⊆` of Kollár (3.88.2). -/
private theorem iterate_derivativeIdealOfRing_le (G : ℕ → Ideal A) (m : ℕ)
    (hG : ∀ j < m, pSpan d (G j) ≤ G j ⊔ G (j + 1)) :
    ∀ s ≤ m, (derivativeIdealOfRing k)^[s] (G 0) ≤
      ⨆ (j : ℕ) (_ : j ≤ s), (logSpanR k (Ideal.span {t}))^[s - j] (G j) := by
  set L := logSpanR k (A := A) (Ideal.span {t})
  intro s hs
  induction s with
  | zero => exact le_iSup₂_of_le 0 le_rfl le_rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    refine (derivativeIdealOfRing_mono (ih (by omega))).trans ?_
    rw [derivativeIdealOfRing, Ideal.span_le]
    rintro _ ⟨δ, f, hf, rfl⟩
    rw [SetLike.mem_coe]
    induction hf using Submodule.iSup_induction' with
    | mem j x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hj x hx =>
        have hd : δ x ∈ derivativeIdealOfRing k (L^[s - j] (G j)) :=
          Ideal.subset_span ⟨δ, x, hx, rfl⟩
        have h := (derivativeIdealOfRing_le h1 _).trans (sup_le_sup_left
          (pSpan_iterate_le h1 h2 h3 (hG j (by omega)) (s - j)) _) hd
        have hT : ∀ i ≤ s + 1, L^[s + 1 - i] (G i) ≤
            ⨆ (j : ℕ) (_ : j ≤ s + 1), L^[s + 1 - j] (G j) := fun i hi =>
          le_iSup₂_of_le (f := fun j (_ : j ≤ s + 1) => L^[s + 1 - j] (G j)) i hi le_rfl
        have e1 : L (L^[s - j] (G j)) = L^[s + 1 - j] (G j) := by
          rw [← Function.iterate_succ_apply' L, Nat.succ_sub hj]
        have e2 : L^[s - j] (G (j + 1)) = L^[s + 1 - (j + 1)] (G (j + 1)) := by
          rw [show s + 1 - (j + 1) = s - j by omega]
        have h1' : L (L^[s - j] (G j)) ≤ ⨆ (j : ℕ) (_ : j ≤ s + 1), L^[s + 1 - j] (G j) := by
          rw [e1]; exact hT j (by omega)
        have h3' : L^[s - j] (G (j + 1)) ≤ ⨆ (j : ℕ) (_ : j ≤ s + 1), L^[s + 1 - j] (G j) := by
          rw [e2]; exact hT (j + 1) (by omega)
        exact SetLike.le_def.1 (sup_le h1' (sup_le ((le_logSpanR h2 h3 _).trans h1') h3')) h
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb

end

end Ring

private theorem isNonzeroAtGenericPoints_mono {X : Scheme} {I J : X.IdealSheafData}
    (hI : IsNonzeroAtGenericPoints I) (h : I ≤ J) : IsNonzeroAtGenericPoints J :=
  fun η hη hbot => hI η hη (eq_bot_iff.2 (hbot ▸ stalk_le_stalk_of_le h η))

/-- A centre along which an ideal nonzero at the generic points has order `≥ 1` contains no
irreducible component of `X`. -/
private theorem hasComponentsOfPositiveCodim_support {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (Z : X.IdealSheafData)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm : 1 ≤ m)
    (hord : OrderAlongGE I (Z.support : Set X) m) :
    HasComponentsOfPositiveCodim (Z.support : Set X) := by
  have hred : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x =>
    have := isRegularLocalRing_stalk_of_smooth_over_field sX x
    have : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain _
    isReduced_of_noZeroDivisors
  have : IsReduced X := @isReduced_of_isReduced_stalk X hred
  intro W hW
  by_contra hlt
  have hcod : codimension (irreducibleClosure hW.1.1) = 0 := by
    rw [codimension_eq_coheight] at hlt ⊢
    exact ENat.lt_one_iff_eq_zero.1 (not_le.1 hlt)
  rw [codimension_eq_coheight, Order.coheight_eq_zero] at hcod
  set η := hW.1.1.genericPoint
  have hgen : closure ({η} : Set X) = closure W := hW.1.1.isGenericPoint_genericPoint_closure
  have hcomp : closure ({η} : Set X) ∈ irreducibleComponents X := by
    rw [hgen]
    refine ⟨hW.1.1.closure, fun C hC hWC => ?_⟩
    let C' : TopologicalSpace.IrreducibleCloseds X := ⟨closure C, hC.closure, isClosed_closure⟩
    have := hcod (b := C') (show closure W ⊆ closure C from hWC.trans subset_closure)
    exact subset_closure.trans this
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents X η hcomp
  have h1 : (1 : ℕ∞) ≤ multAt I η := le_trans (by exact_mod_cast hm) (hord W hW)
  unfold multAt at h1
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by simp, natCast_le_idealOrder_iff', pow_one] at h1
  let := hfield.toField
  exact hI η hcomp (le_bot_iff.1 (h1.trans_eq (IsLocalRing.maximalIdeal_eq_bot)))

/-- The one-step sequence blowing up `Z` is an order-`≥ m` sequence for `(I, m)`. -/
private theorem isOrderGePlainSeq_cons_blowUp {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)]
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm : 1 ≤ m)
    (hord : OrderAlongGE I (Z.support : Set X) m) :
    ClosedBlowupSequence.IsOrderGePlainSeq sX ⟨I, m⟩ (.cons Z (.nil (blowUp Z))) := by
  have hXs : MMP.Mori.IsSmoothScheme sX := isSmoothScheme_of_smooth sX
  have hZs : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX) := isSmoothScheme_of_smooth _
  have hcodim := hasComponentsOfPositiveCodim_support sX Z hI hm hord
  have hmul := MarkedIdeal.birationalTransform_mul_eq sX hXs Z hZs hcodim ⟨I, m⟩ hord
  exact ⟨hXs, hI, hZs, hcodim, hord,
    @isSmoothScheme_of_smooth _ _ _
      (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z ⟨hXs, hZs⟩).1,
    isNonzeroAtGenericPoints_mono (isNonzeroAtGenericPoints_comap_blowUpToBase Z hI)
      (hmul.symm.le.trans (mul_le_of_le_one_right' le_top))⟩

/-- The inclusion `⊇`: every summand `D^{s-j}(-log S₁)(𝒪((m-j)F)·π^*D^j I)` lies in
`D^s(𝒪(mF)·π^*I)`. -/
private theorem iSup_le_higherDerivativeIdeal_birationalTransform
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ sX)) (hZS : S ≤ Z)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm : 1 ≤ m)
    (hord : OrderAlongGE I (Z.support : Set X) m) {s : ℕ} (hs : s ≤ m) :
    ⨆ (j : ℕ) (_ : j ≤ s),
        higherLogDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift S.subschemeι Z).ker
          (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX I j, m - j⟩).I (s - j) ≤
      higherDerivativeIdeal (blowUpToBase Z ≫ sX)
        (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I s := by
  have hB := isOrderGePlainSeq_cons_blowUp sX Z hI hm hord
  have hcent : (ClosedBlowupSequence.cons Z (.nil (blowUp Z))).CentersContainedIn
      S.subschemeι := ⟨by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hZS, trivial⟩
  refine iSup₂_le fun j hj => ?_
  obtain ⟨J, hJ, hJle⟩ := ClosedBlowupSequence.higherLogDerivativeIdeal_derivedTransformJ_le sX
    hX hdim ⟨I, m⟩ hI _ hB hS hcent hj hs
  have h2 := (ClosedBlowupSequence.isOrderGePlainSeq_higherDerivativeIdeal sX hX hdim ⟨I, m⟩ hI
    _ hB j (hj.trans hs)).2 1 le_rfl
  rw [show (ClosedBlowupSequence.cons Z (.nil (blowUp Z))).truncate 1 =
    .cons Z (.nil (blowUp Z)) from rfl, hJ, Option.some_inj] at h2
  subst h2
  rw [← Category.id_comp (blowUpToBase Z)]
  exact hJle

section Geometry

/-! ### Ideal sheaves on affine opens -/

private theorem presheaf_map_refl {Y : Scheme.{u}} {U : Y.Opens} {h : U ≤ U} (s : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h).op).hom s = s := by
  rw [show (homOfLE h).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- An inclusion of ideal sheaves on `Y`, with `f : Y ⟶ X` and `X` locally of finite type over
a field, may be checked on affine opens around the points of `f⁻¹ U` for a neighbourhood `U` of
each closed point of `X`. -/
private theorem le_of_forall_closedPoints {k : Type u} [Field k] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {I J : Y.IdealSheafData}
    (H : ∀ p ∈ closedPoints X, ∃ U : X.Opens, p ∈ U ∧ ∀ q ∈ f ⁻¹ᵁ U,
      ∃ W : Y.affineOpens, q ∈ W.1 ∧ I.ideal W ≤ J.ideal W) : I ≤ J := by
  let V : X.Opens := sSup {U | ∀ q ∈ f ⁻¹ᵁ U, ∃ W : Y.affineOpens, q ∈ W.1 ∧ I.ideal W ≤ J.ideal W}
  have hV : V = ⊤ := Bridges.eq_top_of_closedPoints_subset sX V fun p hp => by
    obtain ⟨U, hpU, hU⟩ := H p hp
    exact (le_sSup (α := X.Opens) hU : U ≤ V) hpU
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun W : {W : Y.affineOpens // I.ideal W ≤ J.ideal W} => W.1) ?_ fun W => W.2
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨U, hU, hqU⟩ := TopologicalSpace.Opens.mem_sSup.1 (hV ▸ trivial : f q ∈ V)
  obtain ⟨W, hqW, hW⟩ := hU q hqU
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW⟩, hqW⟩

/-- The sections of `D^n(-log S)(K)` over an affine open are the iterated logarithmic
derivative ideals of `K(W)` along `S(W)`. -/
private theorem higherLogDerivativeIdeal_ideal {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S K : Y.IdealSheafData)
    (W : Y.affineOpens) (n : ℕ) :
    (higherLogDerivativeIdeal sY S K n).ideal W =
      letI := MMP.Mori.sectionAlgebra sY W.1
      (logSpanR k (S.ideal W))^[n] (K.ideal W) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [higherLogDerivativeIdeal, Function.iterate_succ_apply', logDerivativeIdeal_ideal,
      Function.iterate_succ_apply', ← ih]
    rfl

/-- An inclusion of ideal sheaves restricted to an open `V` gives the inclusion of their
sections over every affine open contained in `V`. -/
private theorem ideal_le_of_comap_ι_le {Y : Scheme.{u}} (V : Y.Opens) {I J : Y.IdealSheafData}
    (h : I.comap V.ι ≤ J.comap V.ι) (W : Y.affineOpens) (hW : W.1 ≤ V) :
    I.ideal W ≤ J.ideal W := by
  have hW' : IsAffineOpen (V.ι ⁻¹ᵁ W.1) :=
    W.2.preimage_of_isOpenImmersion _ (by simpa using hW)
  have hh := Scheme.IdealSheafData.ideal_mono h ⟨_, hW'⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Ideal.comap_le_comap_iff_of_surjective _ (ConcreteCategory.bijective_of_isIso
      ((V.ι.appIso (V.ι ⁻¹ᵁ W.1)).inv)).2] at hh
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ W.1) = W.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hW
  have he' : (⟨V.ι ''ᵁ (V.ι ⁻¹ᵁ W.1), (hW'.image_of_isOpenImmersion _)⟩ : Y.affineOpens) = W :=
    Subtype.ext he
  exact he' ▸ hh

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The blow-up of a smooth `k`-scheme along a smooth centre is smooth over `k`. -/
private theorem smooth_blowUpToBase_comp (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)] : Smooth (blowUpToBase Z ≫ sX) :=
  (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z
    ⟨isSmoothScheme_of_smooth sX, isSmoothScheme_of_smooth _⟩).1

/-- The irreducible components of the blow-up have positive dimension when those of `X` do. -/
private theorem topologicalKrullDim_pos_blowUp (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)]
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C) :
    ∀ C ∈ irreducibleComponents (blowUp Z), 0 < topologicalKrullDim C := by
  intro C hC
  obtain ⟨D, hD, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX Z hC
  exact h ▸ hdim D hD

/-! ### Off the centre -/

/-- Over `X ∖ Z` the blow-up is an isomorphism, `G_0 = π^*I` and `π^*D^s I ⊆ G_s`, so
`D^s(G_0) ⊆ G_s`. -/
private theorem off_center (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ sX)] (I : X.IdealSheafData) (m s : ℕ)
    (hmul : (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I * Z.comap (blowUpToBase Z) ^ m =
      I.comap (blowUpToBase Z))
    (W : (blowUp Z).affineOpens)
    (hW : W.1 ≤ blowUpToBase Z ⁻¹ᵁ ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩) :
    (higherDerivativeIdeal (blowUpToBase Z ≫ sX)
        (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I s).ideal W ≤
      (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX I s, m - s⟩).I.ideal W := by
  set π := blowUpToBase Z
  set U : X.Opens := Z.support.compl
  set V : (blowUp Z).Opens := π ⁻¹ᵁ U
  have hiso := isIso_blowUpToBase_restrict_compl_support Z
  have hVπ : V.ι ≫ π = (π ∣_ U) ≫ U.ι := (morphismRestrict_ι π U).symm
  have : Smooth (V.ι ≫ π) := hVπ ▸ inferInstance
  have := smooth_blowUpToBase_comp sX Z
  have hZU : Z.comap U.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    ext x
    exact ⟨fun h => (x.2 h).elim, fun h => h.elim⟩
  have hF : (Z.comap π).comap V.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, hVπ, Scheme.IdealSheafData.comap_comp, hZU,
      Scheme.IdealSheafData.comap_top]
  have hG : (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I.comap V.ι = I.comap (V.ι ≫ π) := by
    have h := congrArg (Scheme.IdealSheafData.comap · V.ι) hmul
    rw [Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_pow, hF,
      ← Scheme.IdealSheafData.one_eq_top, one_pow, mul_one] at h
    rw [h, Scheme.IdealSheafData.comap_comp]
  refine ideal_le_of_comap_ι_le V ?_ W hW
  rw [comap_higherDerivativeIdeal (π ≫ sX) V.ι (V.ι ≫ π ≫ sX) rfl
      (topologicalKrullDim_pos_blowUp sX Z hdim), hG,
    ← comap_higherDerivativeIdeal sX (V.ι ≫ π) (V.ι ≫ π ≫ sX) (by simp) hdim,
    Scheme.IdealSheafData.comap_comp]
  exact Scheme.IdealSheafData.comap_mono _ (le_idealColon _ _)

/-! ### The charts at the centre -/

/-- The cancellation `J · (e) = (e g) ⟹ J = (g)` for a nonzerodivisor `e`. -/
private theorem eq_span_of_mul_span_eq {R : Type*} [CommRing R] {J : Ideal R} {e g : R}
    (he : e ∈ nonZeroDivisors R) (h : J * Ideal.span {e} = Ideal.span {e * g}) :
    J = Ideal.span {g} := by
  apply le_antisymm
  · intro j hj
    have : j * e ∈ Ideal.span {e * g} := h ▸ Ideal.mul_mem_mul hj (Ideal.mem_span_singleton_self e)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
    have : e * j = e * (c * g) := by rw [mul_comm e j, ← hc]; ring
    rw [(mul_cancel_left_mem_nonZeroDivisors he).1 this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have : e * g ∈ J * Ideal.span {e} := h ▸ Ideal.mem_span_singleton_self _
    obtain ⟨z, hz, hze⟩ := Submodule.mem_mul_span_singleton.1 this
    have : e * z = e * g := by rw [mul_comm, hze]
    exact (mul_cancel_left_mem_nonZeroDivisors he).1 this ▸ hz

open MMP.Flips.ResolutionInputs in
/-- On the chart `U_ℓ` of `B_Z X` over `U` with `S|_U = (x_1)`, the ideal of `S₁` is
`(x_1/x_ℓ)`. -/
private theorem ideal_chart_eq_span_chartFraction {Z S : X.IdealSheafData}
    (c : BlowupChartData Z) (hU : IsAffineOpen c.U) (ℓ i0 : Fin c.r)
    (he : c.chartPullback ℓ (c.x ℓ) ∈ nonZeroDivisors Γ(blowUp Z, c.chart ℓ))
    (hSU : S.ideal ⟨c.U, hU⟩ = Ideal.span {c.x i0}) {T : (blowUp Z).IdealSheafData}
    (hT : T * Z.comap (blowUpToBase Z) = S.comap (blowUpToBase Z)) :
    T.ideal ⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩ = Ideal.span {chartFraction c ℓ i0} := by
  set W : (blowUp Z).affineOpens := ⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩
  set e := c.chartPullback ℓ (c.x ℓ)
  have hpull : ∀ i, c.chartPullback ℓ (c.x i) = e * chartFraction c ℓ i := fun i => by
    rw [chartPullback_eq_chartFraction_mul, mul_comm]
  have happ : ∀ s : Γ(X, c.U), ((blowUpToBase Z).appLE c.U (c.chart ℓ) (c.chart_le ℓ)).hom s =
      c.chartPullback ℓ s := fun _ => rfl
  have hE : (Z.comap (blowUpToBase Z)).ideal W = Ideal.span {e} := by
    rw [Stacks.IdealSheaf.ideal_comap_appLE Z (blowUpToBase Z) ⟨c.U, hU⟩ W (c.chart_le ℓ),
      c.generates ⟨c.U, hU⟩ le_rfl, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      change ((blowUpToBase Z).appLE c.U (c.chart ℓ) (c.chart_le ℓ)).hom
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x i)) ∈ Ideal.span {e}
      rw [presheaf_map_refl, happ, hpull]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self e)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      refine Ideal.subset_span ⟨_, ⟨ℓ, rfl⟩, ?_⟩
      change ((blowUpToBase Z).appLE c.U (c.chart ℓ) (c.chart_le ℓ)).hom
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)) = e
      rw [presheaf_map_refl, happ]
  have hS : (S.comap (blowUpToBase Z)).ideal W = Ideal.span {e * chartFraction c ℓ i0} := by
    rw [Stacks.IdealSheaf.ideal_comap_appLE S (blowUpToBase Z) ⟨c.U, hU⟩ W (c.chart_le ℓ), hSU,
      Ideal.map_span, Set.image_singleton, happ, hpull]
  have h := congrArg (fun J : (blowUp Z).IdealSheafData => J.ideal W) hT
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hE, hS] at h
  exact eq_span_of_mul_span_eq he h

/-- If `π^*f_i = y_ℓ^a g_i` for generators `f_i` of `K` on `U`, then the pull-back of every
section of `K` over `U` is `y_ℓ^a` times an element of the ideal generated by the `g_i`. -/
private theorem exists_chartPullback_eq_pow_mul {Z : X.IdealSheafData} (c : BlowupChartData Z)
    (ℓ : Fin c.r) {n : ℕ} (f : Fin n → Γ(X, c.U)) (g : Fin n → Γ(blowUp Z, c.chart ℓ)) (a : ℕ)
    (hfg : ∀ i, c.chartPullback ℓ (f i) = c.chartPullback ℓ (c.x ℓ) ^ a * g i) :
    ∀ v ∈ Ideal.span (Set.range f), ∃ w ∈ Ideal.span (Set.range g),
      c.chartPullback ℓ v = c.chartPullback ℓ (c.x ℓ) ^ a * w := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact ⟨g i, Ideal.subset_span ⟨i, rfl⟩, hfg i⟩
  | zero => exact ⟨0, zero_mem _, by simp [BlowupChartData.chartPullback]⟩
  | add v v' _ _ hv hv' =>
    obtain ⟨w, hw, e⟩ := hv
    obtain ⟨w', hw', e'⟩ := hv'
    refine ⟨w + w', add_mem hw hw', ?_⟩
    simp only [BlowupChartData.chartPullback, map_add] at e e' ⊢
    rw [e, e', mul_add]
  | smul b v _ hv =>
    obtain ⟨w, hw, e⟩ := hv
    refine ⟨c.chartPullback ℓ b * w, Ideal.mul_mem_left _ _ hw, ?_⟩
    simp only [BlowupChartData.chartPullback, smul_eq_mul, map_mul] at e ⊢
    rw [e]; ring

/-- Where the ideal of `S₁` is the unit ideal, logarithmic derivations are all derivations, and
`D^s(G_0)` is the `j = 0` summand. -/
private theorem le_iSup_of_ideal_eq_top {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] {S₁ : Y.IdealSheafData} (W : Y.affineOpens) (hS : S₁.ideal W = ⊤)
    (G : ℕ → Y.IdealSheafData) (s : ℕ) :
    (higherDerivativeIdeal sY (G 0) s).ideal W ≤
      (⨆ (j : ℕ) (_ : j ≤ s), higherLogDerivativeIdeal sY S₁ (G j) (s - j)).ideal W := by
  let := MMP.Mori.sectionAlgebra sY W.1
  have hL : logSpanR k (⊤ : Ideal Γ(Y, W)) = derivativeIdealOfRing k := by
    funext K
    unfold logSpanR derivativeIdealOfRing
    congr 1
    ext g
    exact ⟨fun ⟨δ, _, f, hf, e⟩ => ⟨δ, f, hf, e⟩,
      fun ⟨δ, f, hf, e⟩ => ⟨δ, fun _ _ => Submodule.mem_top, f, hf, e⟩⟩
  refine le_trans ?_ (Scheme.IdealSheafData.ideal_mono
    (le_iSup₂_of_le (f := fun j (_ : j ≤ s) => higherLogDerivativeIdeal sY S₁ (G j) (s - j))
      0 (Nat.zero_le _) le_rfl) W)
  rw [higherDerivativeIdeal_ideal, higherLogDerivativeIdeal_ideal, hS, hL, Nat.sub_zero]
  rfl

open MMP.Flips.ResolutionInputs in
/-- The `ℓ`-th chart coordinate on `U_ℓ` is the pull-back of `x_ℓ`. -/
private theorem chartCoordinates_castLE_self {Z : X.IdealSheafData} (c : BlowupChartData Z)
    {N : ℕ} (x : Fin N → Γ(X, c.U)) (hrn : c.r ≤ N) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i))
    (ℓ : Fin c.r) : chartCoordinates c x ℓ (Fin.castLE hrn ℓ) = c.chartPullback ℓ (c.x ℓ) := by
  have h : ((Fin.castLE hrn ℓ : Fin N) : ℕ) < c.r := ℓ.2
  rw [chartCoordinates, dite_eq_left h, ite_eq_left (Fin.ext rfl : (⟨_, h⟩ : Fin c.r) = ℓ),
    ← hcx]

open MMP.Flips.ResolutionInputs in
/-- **The chart computation** (Kollár (3.88.2)). On the chart `U_ℓ`, `ℓ ≠ 1`, of the blow-up
over `U`, where `S₁ = (y_1)` for the chart coordinate `y_1 = x_1/x_ℓ`, the sections of `D^s(G_0)`
lie in those of `∑_{j ≤ s} D^{s-j}(-log S₁)(G_j)`. -/
private theorem chart_le_iSup (sX : X ⟶ Spec (.of k)) [Smooth sX] {Z : X.IdealSheafData}
    [Smooth (blowUpToBase Z ≫ sX)] (c : BlowupChartData Z) (hU : IsAffineOpen c.U) {N : ℕ}
    (x : Fin N → Γ(X, c.U)) (hx : IsLocalCoordinates sX c.U x) (hrn : c.r ≤ N)
    (hcx : ∀ i, c.x i = x (Fin.castLE hrn i)) (ℓ i0 : Fin c.r) (hne : i0 ≠ ℓ)
    {S₁ : (blowUp Z).IdealSheafData}
    (hS₁ : S₁.ideal ⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩ = Ideal.span {chartFraction c ℓ i0})
    {I : X.IdealSheafData} {m : ℕ}
    (hIF : ∀ j ≤ m, (higherDerivativeIdeal sX I j).comap (blowUpToBase Z) ≤
      Z.comap (blowUpToBase Z) ^ (m - j))
    {s : ℕ} (hs : s ≤ m) :
    (higherDerivativeIdeal (blowUpToBase Z ≫ sX)
        (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I s).ideal
        ⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩ ≤
      (⨆ (j : ℕ) (_ : j ≤ s),
        higherLogDerivativeIdeal (blowUpToBase Z ≫ sX) S₁
          (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX I j, m - j⟩).I
            (s - j)).ideal ⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩ := by
  classical
  set π := blowUpToBase Z
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hxOn := isLocalCoordinatesOn_of_isLocalCoordinates sX hU hx
  have hU' := isAffineOpen_chart c hU ℓ
  have hz := isLocalCoordinates_chartCoordinates c sX hU x hx hrn hcx ℓ
  have hy := isLocalCoordinatesOn_of_isLocalCoordinates (π ≫ sX) hU' hz
  set e := c.chartPullback ℓ (c.x ℓ) with he_def
  have hzℓ : chartCoordinates c x ℓ (Fin.castLE hrn ℓ) = e :=
    chartCoordinates_castLE_self c x hrn hcx ℓ
  have hz0 : chartCoordinates c x ℓ (Fin.castLE hrn i0) = chartFraction c ℓ i0 :=
    chartCoordinates_castLE_of_ne c x hrn hne
  have hreg : e ∈ nonZeroDivisors Γ(blowUp Z, c.chart ℓ) :=
    hzℓ ▸ mem_nonZeroDivisors_of_isLocalCoordinates (π ≫ sX) hU' hz _
  set W : (blowUp Z).affineOpens := ⟨c.chart ℓ, hU'⟩
  set U' : X.affineOpens := ⟨c.U, hU⟩
  have : IsNoetherianRing Γ(X, c.U) := IsLocallyNoetherian.component_noetherian U'
  have data : ∀ j ≤ m, ∃ (n : ℕ) (f : Fin n → Γ(X, c.U)) (g : Fin n → Γ(blowUp Z, c.chart ℓ)),
      (∀ i, c.chartPullback ℓ (f i) = e ^ (m - j) * g i) ∧
      (higherDerivativeIdeal sX I j).ideal U' = Ideal.span (Set.range f) ∧
      (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX I j, m - j⟩).I.ideal W =
        Ideal.span (Set.range g) := by
    intro j hj
    obtain ⟨n, f, hfU⟩ := Submodule.fg_iff_exists_fin_generating_family.1
      (IsNoetherian.noetherian ((higherDerivativeIdeal sX I j).ideal U'))
    have hf : ∀ (V : X.affineOpens) (h : V.1 ≤ c.U),
        (higherDerivativeIdeal sX I j).ideal V =
          Ideal.span (Set.range fun i => (X.presheaf.map (homOfLE h).op).hom (f i)) := by
      intro V h
      rw [← (higherDerivativeIdeal sX I j).map_ideal (U := V) (V := U') h, ← hfU, Ideal.map_span,
        ← Set.range_comp]
      rfl
    obtain ⟨g, hg, hgen⟩ := c.exists_birationalTransform_ideal_eq_span_chartTransform ℓ
      ⟨higherDerivativeIdeal sX I j, m - j⟩ (hIF j hj) f hf
    have hfg : ∀ i, c.chartPullback ℓ (f i) = e ^ (m - j) * g i := by
      intro i
      have hinj := IsLocalization.injective (Localization.Away e) ((Submonoid.powers_le).2 hreg)
      apply hinj
      have := hg i
      rw [BlowupChartData.chartTransform, Localization.mk_eq_mk',
        IsLocalization.eq_mk'_iff_mul_eq] at this
      rw [map_mul, ← this, mul_comm]
    refine ⟨n, f, g, hfg, hfU.symm, ?_⟩
    rw [hgen W le_rfl]
    simp only [presheaf_map_refl]
    rfl
  choose n f g hfg hfU hgW using data
  let := MMP.Mori.sectionAlgebra (π ≫ sX) W.1
  set t := chartFraction c ℓ i0
  set d := Bridges.partialDerivation hy W le_rfl (Fin.castLE hrn i0)
  set d' := Bridges.partialDerivation hy W le_rfl (Fin.castLE hrn ℓ)
  have hres : ∀ y : Γ(blowUp Z, c.chart ℓ), restrictSection W le_rfl y = y :=
    presheaf_map_refl
  have hcoord : ∀ i j : Fin N, partialDerivative hy W le_rfl i (chartCoordinates c x ℓ j) =
      if i = j then 1 else 0 := fun i j => by
    rw [← hres (chartCoordinates c x ℓ j)]
    exact Bridges.partialDerivative_restrictSection_coordinate hy W le_rfl i j
  have hne' : Fin.castLE hrn ℓ ≠ Fin.castLE hrn i0 := fun h =>
    hne (Fin.castLE_injective hrn h).symm
  have h1 : d t = 1 := by
    change partialDerivative hy W le_rfl _ t = 1
    rw [← hz0, hcoord, ite_eq_left_iff.2 fun h => (h rfl).elim]
  have h2 : d' t = 0 := by
    change partialDerivative hy W le_rfl _ t = 0
    rw [← hz0, hcoord, ite_eq_right_iff.2 fun h => (hne' h).elim]
  have h3 : d' e = 1 := by
    change partialDerivative hy W le_rfl _ e = 1
    rw [← hzℓ, hcoord, ite_eq_left_iff.2 fun h => (h rfl).elim]
  set G : ℕ → Ideal Γ(blowUp Z, c.chart ℓ) := fun j =>
    (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX I j, m - j⟩).I.ideal W
  -- `∂_{y_1} G_j ⊆ G_{j+1}` on the generators
  have key : ∀ (j : ℕ) (hj : j < m) (i : Fin (n j hj.le)), d (g j hj.le i) ∈ G (j + 1) := by
    intro j hj i
    have hchart := Kollar.appLE_partialDerivative_eq_pow_mul_partialDerivative_of_ne c hxOn hrn
      hcx ℓ hy (m := m - j) (by omega) (hfg j hj.le i) hne U' le_rfl W le_rfl (c.chart_le ℓ)
    rw [hres, hres] at hchart
    have hmem : partialDerivative hxOn U' le_rfl (Fin.castLE hrn i0)
        (restrictSection U' le_rfl (f j hj.le i)) ∈
          (higherDerivativeIdeal sX I (j + 1)).ideal U' := by
      rw [higherDerivativeIdeal_succ, derivativeIdeal_ideal]
      let := MMP.Mori.sectionAlgebra sX U'.1
      refine Ideal.subset_span ⟨Bridges.partialDerivation hxOn U' le_rfl (Fin.castLE hrn i0),
        _, ?_, rfl⟩
      rw [restrictSection, presheaf_map_refl, hfU j hj.le]
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [hfU (j + 1) hj] at hmem
    obtain ⟨w, hw, hwe⟩ := exists_chartPullback_eq_pow_mul c ℓ (f (j + 1) hj) (g (j + 1) hj)
      (m - (j + 1)) (hfg (j + 1) hj) _ hmem
    have hwe' : e ^ (m - j - 1) * d (g j hj.le i) = e ^ (m - j - 1) * w := by
      rw [Nat.sub_sub, ← hwe]
      exact hchart.symm
    rw [(mul_cancel_left_mem_nonZeroDivisors (pow_mem hreg _)).1 hwe']
    change w ∈ (MarkedIdeal.birationalTransform Z
      ⟨higherDerivativeIdeal sX I (j + 1), m - (j + 1)⟩).I.ideal W
    rw [hgW (j + 1) hj]
    exact hw
  have hG : ∀ j < m, pSpan d (G j) ≤ G j ⊔ G (j + 1) := by
    intro j hj
    rw [pSpan_le_iff]
    intro v hv
    have hGj : Ideal.span (Set.range (g j hj.le)) ≤ G j := (hgW j hj.le).symm.le
    change v ∈ (MarkedIdeal.birationalTransform Z
      ⟨higherDerivativeIdeal sX I j, m - j⟩).I.ideal W at hv
    rw [hgW j hj.le] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact Ideal.mem_sup_right (key j hj i)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a v hv ih =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine add_mem (Ideal.mul_mem_left _ a ih) (Ideal.mem_sup_left ?_)
      exact Ideal.mul_mem_right _ _ (hGj hv)
  have hring := iterate_derivativeIdealOfRing_le h1 h2 h3 G m hG s hs
  rw [higherDerivativeIdeal_ideal]
  refine hring.trans (iSup₂_le fun j hj => ?_)
  rw [← hS₁]
  refine le_trans (le_of_eq (higherLogDerivativeIdeal_ideal (π ≫ sX) S₁ _ W (s - j)).symm) ?_
  exact Scheme.IdealSheafData.ideal_mono (le_iSup₂_of_le
    (f := fun j (_ : j ≤ s) => higherLogDerivativeIdeal (π ≫ sX) S₁
      (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX I j, m - j⟩).I (s - j))
    j hj le_rfl) W

/-- The quotient of `𝒪_{X,p}` by the stalk of a closed subscheme `D` smooth over `k` is formally
smooth over the stalk of the base. -/
private theorem formallySmooth_quotient_stalk (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData)
    [Smooth (D.subschemeι ≫ f)] (d : D.subscheme) :
    letI := (f.stalkMap (D.subschemeι d)).hom.toAlgebra
    Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (f (D.subschemeι d)))
      (X.presheaf.stalk (D.subschemeι d) ⧸
        AlgebraicGeometry.IdealSheafData.stalk D (D.subschemeι d)) := by
  have : LocallyOfFinitePresentation (D.subschemeι ≫ f) :=
    instLocallyOfFinitePresentationOfSmooth _
  let _ := (f.stalkMap (D.subschemeι d)).hom.toAlgebra
  let _ : Algebra ((Spec (.of k)).presheaf.stalk (f (D.subschemeι d)))
    (D.subscheme.presheaf.stalk d) := ((D.subschemeι ≫ f).stalkMap d).hom.toAlgebra
  have hfs : Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (f (D.subschemeι d)))
      (D.subscheme.presheaf.stalk d) := by
    have : d ∈ (D.subschemeι ≫ f).smoothLocus := by
      rw [Scheme.Hom.smoothLocus_eq_top]
      trivial
    exact this
  let e : (X.presheaf.stalk (D.subschemeι d) ⧸
      AlgebraicGeometry.IdealSheafData.stalk D (D.subschemeι d)) ≃ₐ[
        (Spec (.of k)).presheaf.stalk (f (D.subschemeι d))] D.subscheme.presheaf.stalk d :=
    AlgEquiv.ofRingEquiv (f := MMP.Flips.ResolutionInputs.stalkQuotientEquiv D d) (fun a => by
      change (D.subschemeι.stalkMap d).hom ((f.stalkMap (D.subschemeι d)).hom a) =
        ((D.subschemeι ≫ f).stalkMap d).hom a
      rw [Scheme.Hom.stalkMap_comp]; rfl)
  exact Algebra.FormallySmooth.of_equiv e.symm

open MMP.Flips.ResolutionInputs MMP.Resolution.Bridges in
/-- **Coordinates adapted to the flag `Z ⊆ S ⊆ X`** at a point `p ∈ Z`: an affine open `U ∋ p`
with étale coordinates `x_1, …, x_N` such that `S|_U = (x_1)` and `Z|_U = (x_1, …, x_r)`. -/
private theorem exists_flag_coordinates [CharZero k] (sX : X ⟶ Spec (.of k)) [Smooth sX]
    {S Z : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZS : S ≤ Z) {p : X}
    (hpZ : p ∈ Z.support) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : p ∈ U) (N r : ℕ) (x : Fin N → Γ(X, U)),
      IsLocalCoordinates sX U x ∧ r ≤ N ∧ IsCutOutByFirst S U x 1 ∧
        IsCutOutByFirst Z U x r := by
  classical
  have hX : MMP.Mori.IsSmoothScheme sX := isSmoothScheme_of_smooth sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hpS : p ∈ S.support := Scheme.IdealSheafData.support_antitone hZS hpZ
  have : IsRegularLocalRing (X.presheaf.stalk p) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX p
  have hSreg := isRegularLocalRing_quotient_stalk sX S hS.1 hpS
  have hZreg := isRegularLocalRing_quotient_stalk sX Z hZ hpZ
  have hZsm : letI := (sX.stalkMap p).hom.toAlgebra
      Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (sX p))
        (X.presheaf.stalk p ⧸ IdealSheafData.stalk Z p) := by
    obtain ⟨z, rfl⟩ : ∃ z, Z.subschemeι z = p := by
      rwa [← SetLike.mem_coe, ← Z.range_subschemeι] at hpZ
    have : Smooth (Z.subschemeι ≫ sX) := hZ.smooth
    exact formallySmooth_quotient_stalk sX Z z
  obtain ⟨r, hr⟩ : ∃ r : ℕ, ringKrullDim (X.presheaf.stalk p) =
      ringKrullDim (X.presheaf.stalk p ⧸ IdealSheafData.stalk Z p) + r := by
    have d1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := X.presheaf.stalk p)
    have d2 := IsRegularLocalRing.spanFinrank_maximalIdeal
      (R := X.presheaf.stalk p ⧸ IdealSheafData.stalk Z p)
    have hle := ringKrullDim_quotient_le (IdealSheafData.stalk Z p)
    rw [← d1, ← d2] at hle
    have hle'' : Submodule.spanFinrank (IsLocalRing.maximalIdeal
        (X.presheaf.stalk p ⧸ IdealSheafData.stalk Z p)) ≤
        Submodule.spanFinrank (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) := by
      exact_mod_cast WithBot.coe_le_coe.mp hle
    refine ⟨Submodule.spanFinrank (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) -
      Submodule.spanFinrank (IsLocalRing.maximalIdeal
        (X.presheaf.stalk p ⧸ IdealSheafData.stalk Z p)), ?_⟩
    rw [← d1, ← d2, ← Nat.cast_add, Nat.add_sub_cancel' hle'']
  have hs : ringKrullDim (X.presheaf.stalk p) =
      ringKrullDim (X.presheaf.stalk p ⧸ IdealSheafData.stalk S p) + ((1 : ℕ) : WithBot ℕ∞) := by
    have : IsDomain (X.presheaf.stalk p ⧸ IdealSheafData.stalk S p) :=
      IsRegularLocalRing.isDomain _
    have : (IdealSheafData.stalk S p).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp this
    have hht := height_stalk_eq_one_of_isPureCodimOne S hS.2 (x := p)
    rw [← ringKrullDim_quotient_add_one_of_height_eq_one _ hht, Nat.cast_one]
  obtain ⟨hrN, U, hU, hpU, x, hx, hcutS, hcutZ⟩ :=
    exists_isLocalCoordinates_isCutOutByFirst_of_stalk sX S Z hZS p hSreg hZreg hZsm hs hr
  exact ⟨U, hU, hpU, _, r, x, hx, hrN, hcutS, hcutZ⟩

open MMP.Flips.ResolutionInputs in
/-- The inclusion `⊆`: `D^s(𝒪(mF)·π^*I) ⊆ ∑_{j ≤ s} D^{s-j}(-log S₁)(𝒪((m-j)F)·π^*D^j I)`. -/
private theorem higherDerivativeIdeal_birationalTransform_le_iSup
    [CharZero k] (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ sX)) (hZS : S ≤ Z)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm : 1 ≤ m)
    (hord : OrderAlongGE I (Z.support : Set X) m) {s : ℕ} (hs : s ≤ m) :
    higherDerivativeIdeal (blowUpToBase Z ≫ sX) (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I s ≤
      ⨆ (j : ℕ) (_ : j ≤ s),
        higherLogDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift S.subschemeι Z).ker
          (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX I j, m - j⟩).I (s - j) := by
  classical
  have hXs : MMP.Mori.IsSmoothScheme sX := isSmoothScheme_of_smooth sX
  have hZs : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX) := isSmoothScheme_of_smooth _
  have : LocallyOfFinitePresentation sX := instLocallyOfFinitePresentationOfSmooth _
  have : LocallyOfFiniteType sX := instLocallyOfFiniteTypeOfLocallyOfFinitePresentation sX
  have := smooth_blowUpToBase_comp sX Z
  have : LocallyOfFinitePresentation (blowUpToBase Z ≫ sX) :=
    instLocallyOfFinitePresentationOfSmooth _
  have : LocallyOfFiniteType (blowUpToBase Z ≫ sX) :=
    instLocallyOfFiniteTypeOfLocallyOfFinitePresentation _
  have hcodim := hasComponentsOfPositiveCodim_support sX Z hI hm hord
  have hmul := MarkedIdeal.birationalTransform_mul_eq sX hXs Z hZs hcodim ⟨I, m⟩ hord
  have hB := isOrderGePlainSeq_cons_blowUp sX Z hI hm hord
  have hIF : ∀ j ≤ m, (higherDerivativeIdeal sX I j).comap (blowUpToBase Z) ≤
      Z.comap (blowUpToBase Z) ^ (m - j) := fun j hj =>
    comap_le_comap_pow_of_stalk_le _ _ _ _ (stalk_le_pow_of_orderAlongGE sX hXs Z hZs _ _
      (ClosedBlowupSequence.isOrderGePlainSeq_higherDerivativeIdeal sX hX hdim ⟨I, m⟩ hI _ hB j
        hj).1.2.2.2.2.1)
  have hS₁ := (ker_canonicalLift_subschemeι_mul_comap_eq_comap sX hXs S Z hS hZs hZS).2.1
  refine le_of_forall_closedPoints (blowUpToBase Z) sX fun p _ => ?_
  by_cases hpZ : p ∈ (Z.support : Set X)
  · obtain ⟨U, hU, hpU, N, r, x, hx, hrN, hcutS, hcutZ⟩ := exists_flag_coordinates sX hS hZs hZS hpZ
    let c : BlowupChartData Z :=
      { U := U
        r := r
        x := fun i => x (Fin.castLE hrN i)
        generates := fun V hV => by
          rw [hcutZ V hV]
          congr 1
          ext s
          constructor
          · rintro ⟨i, hi, rfl⟩
            exact ⟨⟨i, hi⟩, rfl⟩
          · rintro ⟨j, rfl⟩
            exact ⟨Fin.castLE hrN j, j.2, rfl⟩ }
    refine ⟨U, hpU, fun q hq => ?_⟩
    have hqU : q ∈ blowUpToBase Z ⁻¹ᵁ c.U := hq
    rw [← iSup_chart_eq_preimage c] at hqU
    obtain ⟨ℓ, hqℓ⟩ := TopologicalSpace.Opens.mem_iSup.mp hqU
    refine ⟨⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩, hqℓ, ?_⟩
    set i0 : Fin c.r := ⟨0, ℓ.pos⟩
    have hSU : S.ideal ⟨c.U, hU⟩ = Ideal.span {c.x i0} := by
      rw [hcutS ⟨U, hU⟩ le_rfl]
      congr 1
      ext s
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        rw [presheaf_map_refl]
        change x i = x (Fin.castLE hrN i0)
        congr 1
        ext
        simp only [Fin.val_castLE, i0]
        omega
      · rintro rfl
        refine ⟨Fin.castLE hrN i0, by simp [i0], ?_⟩
        rw [presheaf_map_refl]
    have hz := isLocalCoordinates_chartCoordinates c sX hU x hx hrN (fun _ => rfl) ℓ
    have hreg : c.chartPullback ℓ (c.x ℓ) ∈ nonZeroDivisors Γ(blowUp Z, c.chart ℓ) :=
      chartCoordinates_castLE_self c x hrN (fun _ => rfl) ℓ ▸
        mem_nonZeroDivisors_of_isLocalCoordinates _ (isAffineOpen_chart c hU ℓ) hz _
    have hT := ideal_chart_eq_span_chartFraction c hU ℓ i0 hreg hSU hS₁
    by_cases hℓ : i0 = ℓ
    · have h1 : chartFraction c ℓ i0 = 1 := by
        refine (mul_cancel_left_mem_nonZeroDivisors hreg).1 ?_
        rw [mul_one, mul_comm, ← chartPullback_eq_chartFraction_mul, hℓ]
      exact le_iSup_of_ideal_eq_top _ _ (by rw [hT, h1, Ideal.span_singleton_one])
        (fun j => (MarkedIdeal.birationalTransform Z
          ⟨higherDerivativeIdeal sX I j, m - j⟩).I) s
    · exact chart_le_iSup sX c hU x hx hrN (fun _ => rfl) ℓ i0 hℓ hT hIF hs
  · refine ⟨⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩, hpZ, fun q hq => ?_⟩
    obtain ⟨W, hW, hqW, hWV⟩ := exists_isAffineOpen_mem_and_subset hq
    refine ⟨⟨W, hW⟩, hqW, ?_⟩
    refine (off_center sX hdim Z I m s hmul ⟨W, hW⟩ hWV).trans ?_
    refine Scheme.IdealSheafData.ideal_mono (le_iSup₂_of_le
      (f := fun j (_ : j ≤ s) => higherLogDerivativeIdeal (blowUpToBase Z ≫ sX)
        (canonicalLift S.subschemeι Z).ker
        (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX I j, m - j⟩).I (s - j))
      s le_rfl ?_) _
    rw [Nat.sub_self]
    exact le_rfl

end Geometry

/-- **Kollár (3.88.2), one blow-up.** Let `X` be smooth, equidimensional and of finite type over a
field `k` of characteristic zero, with irreducible components of positive dimension, `S ⊆ X` a
smooth hypersurface, `Z ⊆ S` a smooth closed subscheme with blow-up `π = blowUpToBase Z`, and
`S₁ ⊆ B_Z X` the birational transform of `S`, cut out by the kernel of
`canonicalLift S.subschemeι Z`. Let `I` be an ideal sheaf nonzero at the generic points of `X`
with `ord_Z I ≥ m`. Then for `s ≤ m`, `D^s(𝒪(mF)·π^*I)` is the sum over `j ≤ s` of
`D^{s-j}(-log S₁)(𝒪((m-j)F)·π^*D^j I)`, where `𝒪((m-j)F)·π^*D^j I` is the ideal of the
birational transform of the marked ideal `(D^j I, m - j)`. -/
@[mmp "lem_kr3d_log_decomposition_one_blowup"]
public theorem higherDerivativeIdeal_birationalTransform_eq_iSup
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : Equidimensional X)
    (hdim : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ sX)) (hZS : S ≤ Z)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ}
    (hord : OrderAlongGE I (Z.support : Set X) m) {s : ℕ} (hs : s ≤ m) :
    higherDerivativeIdeal (blowUpToBase Z ≫ sX) (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I s =
      ⨆ (j : ℕ) (_ : j ≤ s),
        higherLogDerivativeIdeal (blowUpToBase Z ≫ sX) (canonicalLift S.subschemeι Z).ker
          (MarkedIdeal.birationalTransform Z ⟨higherDerivativeIdeal sX I j, m - j⟩).I (s - j) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain rfl : s = 0 := Nat.le_zero.mp hs
    exact le_antisymm (le_iSup₂_of_le 0 le_rfl le_rfl)
      (iSup₂_le fun j hj => by obtain rfl := Nat.le_zero.mp hj; rfl)
  exact le_antisymm
    (higherDerivativeIdeal_birationalTransform_le_iSup sX hX hdim hS Z hZ hZS hI hm hord hs)
    (iSup_le_higherDerivativeIdeal_birationalTransform sX hX hdim hS Z hZ hZS hI hm hord hs)

end LogDecomposition

end MMP.Resolution

end
