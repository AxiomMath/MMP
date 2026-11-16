module
public import MMP.AlgebraicGeometry.Resolution.BlowupChartCoordinates
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagCoordinates
public import MMP.AlgebraicGeometry.Resolution.Blowup.RegularSequenceCharts

/-!
# The birational transform of a smooth hypersurface containing the centre

Let `X` be a smooth scheme over a field `k` of characteristic `0`, `H ⊆ X` a smooth
hypersurface, `Z ⊆ H` a smooth closed subscheme and `π : B_ZX → X` the blow-up, with
exceptional divisor `F = π⁻¹(Z)`. The restriction of the one-step blow-up sequence `B_ZX → X`
to `H` is `B_ZH → H`, and the canonical lift `B_ZH → B_ZX` is a closed immersion whose ideal
sheaf is `𝒪_{B_ZX}(F)·π^*𝒪_X(-H)`; in particular `B_ZH` is a smooth hypersurface of `B_ZX`
(possibly empty).

## Main results

* `MMP.Resolution.ker_canonicalLift_subschemeι_mul_comap_eq_comap`: the statement above.

## Implementation notes

Ideal sheaves are subsheaves of `𝒪`, so `𝒪(F)·π^*𝒪(-H)` is characterised by multiplication
with the invertible ideal `𝒪(-F) = π^*I_Z`: the ideal `I` of `B_ZH` satisfies
`I · π^*I_Z = π^*I_H`. Since `π^*I_Z` is invertible, this determines `I`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.87]
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Resolution

open Limits in
/-- The ideal of the canonical lift `B_{j⁻¹Z}Y → B_ZX` is the ideal of the part of
`Y ×_X B_ZX` off the exceptional divisor, mapped into `B_ZX`. -/
private theorem ker_canonicalLift_eq {X Y : Scheme.{u}} (j : Y ⟶ X) (Z : X.IdealSheafData) :
    (MMP.Resolution.canonicalLift j Z).ker =
      ((Stacks.StrictTransform.exceptionalComplement j (blowUpToBase Z) (exceptionalIdeal Z)).ι ≫
        pullback.snd j (blowUpToBase Z)).ker := by
  set St := Stacks.StrictTransform.ideal j (blowUpToBase Z) (exceptionalIdeal Z) with hSt
  set e := strictTransformBlowUpIso j Z
  have hw := e.inv.w
  simp only [Over.mk_hom] at hw
  have hfst : e.inv.left ≫ St.subschemeι ≫ pullback.fst j (blowUpToBase Z) =
      blowUpToBase (Z.comap j) := hw
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have hfac : e.inv.left ≫ St.subschemeι ≫ pullback.snd j (blowUpToBase Z) =
      MMP.Resolution.canonicalLift j Z := by
    rw [MMP.Resolution.canonicalLift]
    refine blowUpLift_unique _ _ _ _ ?_
    rw [Category.assoc, Category.assoc, ← pullback.condition]
    simpa only [Category.assoc] using congrArg (· ≫ j) hfst
  rw [← hfac, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp,
    Scheme.IdealSheafData.ker_subschemeι, hSt, Stacks.StrictTransform.ideal_eq_ker_ι,
    Scheme.IdealSheafData.map_ker]

open Limits in
private theorem comap_eq_ker_pullback_snd {X Y : Scheme.{u}} (H : X.IdealSheafData) (f : Y ⟶ X) :
    H.comap f = (pullback.snd H.subschemeι f).ker := by
  change (pullback.fst f H.subschemeι).ker = _
  rw [← pullbackSymmetry_hom_comp_fst, Scheme.Hom.ker_comp_of_isIso]

/-- Restrictions to two equal opens vanish together. -/
private theorem res_eq_zero_iff_of_eq {P : Scheme.{u}} {U W₁ W₂ : P.Opens} (h₁ : W₁ ≤ U)
    (h₂ : W₂ ≤ U) (hW : W₁ = W₂) (s : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom s = 0 ↔ (P.presheaf.map (homOfLE h₂).op).hom s = 0 := by
  subst hW
  rfl

/-- A section over `U` is killed by the inclusion of an open `V` exactly when its restriction to
`U ⊓ V` vanishes. -/
private theorem ι_app_eq_zero_iff {P : Scheme.{u}} (V U : P.Opens) (s : Γ(P, U)) :
    (V.ι.app U).hom s = 0 ↔
      (P.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op).hom s = 0 := by
  have hQ : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  have hcomp : (V.ι.appIso (V.ι ⁻¹ᵁ U)).inv.hom ((V.ι.app U).hom s) =
      (P.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op).hom s := by
    rw [← CommRingCat.comp_apply]
    exact congrArg (fun φ : Γ(P, U) ⟶ Γ(P, V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) ↦ φ.hom s)
      (Scheme.Hom.app_appIso_inv V.ι U)
  rw [res_eq_zero_iff_of_eq _ (V.ι.image_preimage_le U) hQ.symm]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← hcomp, h, map_zero]
  · exact (ConcreteCategory.bijective_of_isIso (V.ι.appIso (V.ι ⁻¹ᵁ U)).inv).1
      (by rw [hcomp, h, map_zero])

/-- **The ideal of the part off an effective Cartier divisor, on a chart.** Let `s : P ⟶ B` be
quasi-compact, `E` an ideal sheaf on `B` generated on an affine open `W` by `e`, and
`V = s⁻¹(B ∖ Supp E)`. A section `t` over `W` lies in the ideal of `V → B` exactly when some
power of `e` multiplies it into the ideal of `s`. -/
private theorem mem_ker_ι_comp_iff {P B : Scheme.{u}} (s : P ⟶ B) [QuasiCompact s]
    (E : B.IdealSheafData) [QuasiCompact (s ⁻¹ᵁ E.support.compl).ι] (W : B.affineOpens)
    {e : Γ(B, W.1)} (hE : E.ideal W = Ideal.span {e}) (t : Γ(B, W.1)) :
    t ∈ ((s ⁻¹ᵁ E.support.compl).ι ≫ s).ker.ideal W ↔ ∃ n : ℕ, e ^ n * t ∈ s.ker.ideal W := by
  set V := s ⁻¹ᵁ E.support.compl
  set U := s ⁻¹ᵁ W.1
  have hUc : IsCompact (U : Set P) := QuasiCompact.isCompact_preimage _ W.1.2 W.2.isCompact
  have hsupp : ∀ x ∈ W.1, x ∈ E.support ↔ x ∉ B.basicOpen e := by
    intro x hx
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := W) hx, hE, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    rfl
  have hVU : U ⊓ V = P.basicOpen ((s.app W.1).hom e) := by
    rw [← Scheme.preimage_basicOpen]
    ext q
    change (s q ∈ W.1 ∧ s q ∉ E.support) ↔ s q ∈ B.basicOpen e
    constructor
    · rintro ⟨hq, hqE⟩
      by_contra hne
      exact hqE ((hsupp _ hq).2 hne)
    · intro hq
      exact ⟨B.basicOpen_le e hq, fun hqE => (hsupp _ (B.basicOpen_le e hq)).1 hqE hq⟩
  have step : t ∈ RingHom.ker ((V.ι ≫ s).app W.1).hom ↔
      (V.ι.app U).hom ((s.app W.1).hom t) = 0 := Iff.rfl
  rw [Scheme.Hom.ker_apply (V.ι ≫ s), step, Scheme.Hom.ker_apply s, ι_app_eq_zero_iff,
    res_eq_zero_iff_of_eq _ (P.basicOpen_le _) hVU]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact P hUc
      ((s.app W.1).hom t) ((s.app W.1).hom e) h
    exact ⟨n, by rw [RingHom.mem_ker, map_mul, map_pow, hn]⟩
  · rintro ⟨n, hn⟩
    rw [RingHom.mem_ker, map_mul, map_pow] at hn
    have hu := P.toRingedSpace.isUnit_res_basicOpen ((s.app W.1).hom e)
    have h2 := congrArg (P.presheaf.map (homOfLE (P.basicOpen_le ((s.app W.1).hom e))).op).hom hn
    rw [map_mul, map_pow, map_zero] at h2
    exact (hu.pow n).mul_right_eq_zero.mp h2

/-- If `e` is a nonzerodivisor modulo `g`, the sections multiplied by a power of `e` into `(e g)`
are the multiples of `g`. -/
private theorem eq_span_of_forall_mem_iff {R : Type*} [CommRing R] {e g : R}
    (hreg : IsSMulRegular (R ⧸ Ideal.span {g}) e) (I : Ideal R)
    (hI : ∀ t, t ∈ I ↔ ∃ n : ℕ, e ^ n * t ∈ Ideal.span {e * g}) : I = Ideal.span {g} := by
  ext t
  rw [hI]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
    have hmem : e ^ n * t ∈ Ideal.span {g} :=
      Ideal.mem_span_singleton'.mpr ⟨c * e, by rw [← hc]; ring⟩
    have hr := hreg.pow n
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hr
    exact hr t (by rwa [smul_eq_mul])
  · intro ht
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    exact ⟨1, Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩⟩

open MvPolynomial in
/-- Distinct variables of a polynomial ring form a weakly regular sequence. -/
private theorem isWeaklyRegular_ofFn_X_comp {R : Type*} [CommRing R] {τ : Type*} {m : ℕ}
    (σ : Fin m → τ) (hσ : Function.Injective σ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial τ R)
      (List.ofFn fun j => (X (σ j) : MvPolynomial τ R)) := by
  rw [RingTheory.Sequence.isWeaklyRegular_iff]
  intro i hi
  have hin : i < m := by simpa using hi
  have hset : Ideal.ofList ((List.ofFn fun j => (X (σ j) : MvPolynomial τ R)).take i) =
      Ideal.span (X '' (σ '' {j : Fin m | (j : ℕ) < i})) := by
    rw [← Fin.ofFn_take_eq_take_ofFn hin.le]
    have hs : {r : MvPolynomial τ R | r ∈ List.ofFn (Fin.take i hin.le fun j => X (σ j))}
        = X '' (σ '' {j : Fin m | (j : ℕ) < i}) := by
      refine Set.ext fun r => ?_
      constructor
      · intro hr
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
        exact ⟨σ (Fin.castLE hin.le j), ⟨_, by simp, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, by simp [Fin.take, Fin.castLE]⟩
    exact congrArg Ideal.span hs
  rw [MvPolynomial.ideal_smul_top, hset, isSMulRegular_iff_right_eq_zero_of_smul]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, List.getElem_ofFn,
    smul_eq_mul] at hx
  refine (Submodule.Quotient.mk_eq_zero _).2 (mem_span_X_image_of_X_mul_mem ?_ hx)
  rintro ⟨j, hj, hji⟩
  obtain rfl := hσ hji
  simp at hj

/-- Distinct members of a system of étale local coordinates on an affine open form a weakly
regular sequence: the coordinate map to `𝔸ⁿ` is flat. -/
private theorem isWeaklyRegular_of_isLocalCoordinates {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (x : Fin n → Γ(X, U))
    (hx : MMP.Resolution.IsLocalCoordinates sX U x) {m : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) :
    RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn fun j => x (σ j)) := by
  have : IsAffine U.toScheme := hU
  set h := AffineSpace.homOfVector (n := ULift.{u} (Fin n)) (U.ι ≫ sX)
    fun i => U.topIso.inv.hom (x i.down) with hh
  have : Etale h := hx
  have hflat : RingHom.Flat h.appTop.hom := HasRingHomProperty.appTop @Flat h inferInstance
  let E' : Γ(AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)), ⊤) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) k) :=
    (Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).op).symm ≪≫
      Scheme.ΓSpecIso _
  let E := E'.commRingCatIsoToRingEquiv
  have hE : ∀ i, E.symm (MvPolynomial.X i) = AffineSpace.coord (Spec (.of k)) i := by
    intro i
    apply E.injective
    rw [RingEquiv.apply_symm_apply]
    change _ = (Scheme.ΓSpecIso _).hom.hom
      ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).inv.appTop.hom
        (AffineSpace.coord (Spec (.of k)) i))
    rw [AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]
  let ψ : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, U) :=
    U.topIso.hom.hom.comp (h.appTop.hom.comp E.symm.toRingHom)
  have hψ : ψ.Flat :=
    RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective E.symm.bijective) hflat)
      (RingHom.Flat.of_bijective U.topIso.commRingCatIsoToRingEquiv.bijective)
  have hψX : ∀ i, ψ (MvPolynomial.X i) = x i.down := by
    intro i
    change U.topIso.hom.hom (h.appTop.hom (E.symm (MvPolynomial.X i))) = _
    rw [hE, hh, AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]
  let := ψ.toAlgebra
  have : Module.Flat (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, U) := hψ
  have hreg := (isWeaklyRegular_ofFn_X_comp (R := k) (fun j => ULift.up.{u} (σ j))
    (fun a b hab => hσ (congrArg ULift.down hab))).of_flat (S := Γ(X, U))
  rw [List.map_ofFn] at hreg
  convert hreg using 2
  funext j
  exact (hψX _).symm

/-- A member of a system of étale local coordinates on an affine open is a nonzerodivisor. -/
private theorem isSMulRegular_of_isLocalCoordinates {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (x : Fin n → Γ(X, U))
    (hx : MMP.Resolution.IsLocalCoordinates sX U x) (i : Fin n) :
    IsSMulRegular Γ(X, U) (x i) := by
  have := isWeaklyRegular_of_isLocalCoordinates sX hU x hx (fun _ : Fin 1 => i)
    (fun a b _ => Subsingleton.elim a b)
  simp only [List.ofFn_succ, List.ofFn_zero, RingTheory.Sequence.isWeaklyRegular_cons_iff] at this
  exact this.1

open Pointwise in
/-- Of two distinct members of a system of étale local coordinates on an affine open, the second
is a nonzerodivisor modulo the first. -/
private theorem isSMulRegular_quotient_of_isLocalCoordinates {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (x : Fin n → Γ(X, U)) (hx : MMP.Resolution.IsLocalCoordinates sX U x) {i j : Fin n}
    (hij : i ≠ j) : IsSMulRegular (Γ(X, U) ⧸ Ideal.span {x i}) (x j) := by
  have := isWeaklyRegular_of_isLocalCoordinates sX hU x hx ![i, j] (by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm])
  simp only [List.ofFn_succ, List.ofFn_zero, RingTheory.Sequence.isWeaklyRegular_cons_iff,
    Matrix.cons_val_zero, Matrix.cons_val_succ] at this
  have h2 := this.2.1
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro y hy
  have key : ∀ z : Γ(X, U), z ∈ x i • (⊤ : Submodule Γ(X, U) Γ(X, U)) ↔ z ∈ Ideal.span {x i} := by
    intro z
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, -, rfl⟩
      exact ⟨c, by rw [smul_eq_mul, mul_comm]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, trivial, by rw [smul_eq_mul, mul_comm]⟩
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at h2
  have := h2 (Submodule.Quotient.mk y) (by
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, key])
  rwa [Submodule.Quotient.mk_eq_zero, key] at this

/-- **The ideal of `B_ZH ⊆ B_ZX` on a chart.** Let `W` be an affine open of `B_ZX` on which
`π^*I_Z = (e)` and `π^*I_H = (e g)`, with `e` a nonzerodivisor modulo `g`. Then the ideal of the
canonical lift `B_ZH → B_ZX` is `(g)` on `W`. -/
private theorem ideal_ker_canonicalLift_eq_span {X : Scheme.{u}} (H Z : X.IdealSheafData)
    (W : (blowUp Z).affineOpens) {e g : Γ(blowUp Z, W.1)}
    (hE : (Z.comap (blowUpToBase Z)).ideal W = Ideal.span {e})
    (hK : (H.comap (blowUpToBase Z)).ideal W = Ideal.span {e * g})
    (hreg : IsSMulRegular (Γ(blowUp Z, W.1) ⧸ Ideal.span {g}) e) :
    (MMP.Resolution.canonicalLift H.subschemeι Z).ker.ideal W = Ideal.span {g} := by
  rw [ker_canonicalLift_eq]
  refine eq_span_of_forall_mem_iff hreg _ fun t => ?_
  rw [← hK, comap_eq_ker_pullback_snd]
  exact mem_ker_ι_comp_iff (Limits.pullback.snd H.subschemeι (blowUpToBase Z)) (exceptionalIdeal Z)
    W hE t

private theorem presheaf_map_homOfLE_refl_apply {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE (le_refl U)).op).hom s = s := by
  rw [show (homOfLE (le_refl U)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- A nonzerodivisor is reflected by an injective ring homomorphism. -/
private theorem isSMulRegular_of_injective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) {g : R} (hg : IsSMulRegular S (φ g)) : IsSMulRegular R g :=
  fun a b hab => hφ (hg (by simpa only [smul_eq_mul, map_mul] using congrArg φ hab))

/-- Every scalar acts regularly on a subsingleton module. -/
private theorem isSMulRegular_of_subsingleton {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Subsingleton M] (r : R) : IsSMulRegular M r :=
  fun a b _ => Subsingleton.elim a b

open MMP.Flips.ResolutionInputs in
/-- **The chart computation at the centre** (Kollár 3.87). Let `x_1, …, x_N` be étale
coordinates on an affine open `U` of `X`, the first `r` of which generate `I_Z` and the first of
which generates `I_H`. On the chart `U_ℓ` of `B_ZX`, `π^*I_Z = (π^*x_ℓ)`,
`π^*I_H = (π^*x_ℓ · x_1/x_ℓ)`, and `π^*x_ℓ` is a nonzerodivisor modulo `x_1/x_ℓ`, which is itself a
nonzerodivisor. -/
private theorem exists_good_chart {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (H Z : X.IdealSheafData) (c : MMP.Resolution.BlowupChartData Z)
    (hU : IsAffineOpen c.U) {N : ℕ} (x : Fin N → Γ(X, c.U))
    (hx : MMP.Resolution.IsLocalCoordinates sX c.U x) (hrN : c.r ≤ N)
    (hcx : ∀ i, c.x i = x (Fin.castLE hrN i)) (ℓ : Fin c.r)
    (hH : H.ideal ⟨c.U, hU⟩ = Ideal.span {c.x ⟨0, ℓ.pos⟩}) :
    ∃ e g : Γ(blowUp Z, c.chart ℓ),
      (Z.comap (blowUpToBase Z)).ideal ⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩ = Ideal.span {e} ∧
      (H.comap (blowUpToBase Z)).ideal ⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩ =
        Ideal.span {e * g} ∧
      IsSMulRegular (Γ(blowUp Z, c.chart ℓ) ⧸ Ideal.span {g}) e ∧
      IsSMulRegular Γ(blowUp Z, c.chart ℓ) g := by
  set W : (blowUp Z).affineOpens := ⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩
  set i0 : Fin c.r := ⟨0, ℓ.pos⟩
  set e := c.chartPullback ℓ (c.x ℓ)
  set g := chartFraction c ℓ i0
  have hz := isLocalCoordinates_chartCoordinates c sX hU x hx hrN hcx ℓ
  have hzℓ : chartCoordinates c x ℓ (Fin.castLE hrN ℓ) = e := by
    have h : ((Fin.castLE hrN ℓ : Fin N) : ℕ) < c.r := ℓ.2
    rw [chartCoordinates, dite_eq_left h]
    have hℓ' : (⟨_, h⟩ : Fin c.r) = ℓ := Fin.ext rfl
    rw [ite_eq_left hℓ', ← hcx]
  have he : IsSMulRegular Γ(blowUp Z, c.chart ℓ) e := by
    rw [← hzℓ]
    exact isSMulRegular_of_isLocalCoordinates _ (isAffineOpen_chart c hU ℓ) _ hz _
  have hpull : ∀ i, c.chartPullback ℓ (c.x i) = e * chartFraction c ℓ i := fun i => by
    rw [chartPullback_eq_chartFraction_mul, mul_comm]
  have happ : ∀ s : Γ(X, c.U), ((blowUpToBase Z).appLE c.U (c.chart ℓ) (c.chart_le ℓ)).hom s =
      c.chartPullback ℓ s := fun _ => rfl
  refine ⟨e, g, ?_, ?_, ?_⟩
  · rw [Stacks.IdealSheaf.ideal_comap_appLE Z (blowUpToBase Z) ⟨c.U, hU⟩ W (c.chart_le ℓ),
      c.generates ⟨c.U, hU⟩ le_rfl, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      change ((blowUpToBase Z).appLE c.U (c.chart ℓ) (c.chart_le ℓ)).hom
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x i)) ∈ Ideal.span {e}
      rw [presheaf_map_homOfLE_refl_apply, happ, hpull]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self e)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      refine Ideal.subset_span ⟨_, ⟨ℓ, rfl⟩, ?_⟩
      change ((blowUpToBase Z).appLE c.U (c.chart ℓ) (c.chart_le ℓ)).hom
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)) = e
      rw [presheaf_map_homOfLE_refl_apply, happ]
  · rw [Stacks.IdealSheaf.ideal_comap_appLE H (blowUpToBase Z) ⟨c.U, hU⟩ W (c.chart_le ℓ), hH,
      Ideal.map_span, Set.image_singleton, happ, hpull]
  by_cases hℓ : ℓ = i0
  · have hg1 : g = 1 := by
      apply he
      change e * g = e * 1
      rw [mul_one, ← hpull, ← hℓ]
    have : Subsingleton (Γ(blowUp Z, c.chart ℓ) ⧸ Ideal.span {g}) := by
      rw [hg1, Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact ⟨isSMulRegular_of_subsingleton e, hg1 ▸ IsSMulRegular.one _⟩
  · have h0 : chartCoordinates c x ℓ (Fin.castLE hrN i0) = g :=
      chartCoordinates_castLE_of_ne c x hrN (Ne.symm hℓ)
    have hne : Fin.castLE hrN i0 ≠ Fin.castLE hrN ℓ := fun h =>
      hℓ (Fin.castLE_injective hrN h).symm
    have hq := isSMulRegular_quotient_of_isLocalCoordinates _ (isAffineOpen_chart c hU ℓ) _ hz hne
    rw [h0, hzℓ] at hq
    exact ⟨hq, h0 ▸ isSMulRegular_of_isLocalCoordinates _ (isAffineOpen_chart c hU ℓ) _ hz _⟩

/-- An affine open disjoint from the support of an ideal sheaf is one where the ideal is the unit
ideal. -/
private theorem ideal_eq_top_of_subset_compl_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (h : (U.1 : Set X) ⊆ (I.support : Set X)ᶜ) : I.ideal U = ⊤ := by
  have hzl : X.zeroLocus (U := U.1) (I.ideal U : Set _) ∩ (U.1 : Set X) = ∅ := by
    rw [← Scheme.IdealSheafData.coe_support_inter I U, Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    exact h hz2 hz1
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.image_eq_empty.mp
    ((U.2.fromSpec_image_zeroLocus (I.ideal U : Set _)).trans hzl))

open MMP.Flips.ResolutionInputs in
/-- **The chart computation off the centre.** Over an affine open `U` of `X` disjoint from `Z`
on which `I_H = (h)` with `h` a nonzerodivisor, every point of `π⁻¹(U)` lies in an affine open
of `B_ZX` on which `π^*I_Z = (1)` and `π^*I_H = (π^*h)`, `π^*h` a nonzerodivisor. -/
private theorem exists_good_off_centre {X : Scheme.{u}} (H Z : X.IdealSheafData)
    (U : X.affineOpens) (hUZ : (U.1 : Set X) ⊆ (Z.support : Set X)ᶜ) {h : Γ(X, U.1)}
    (hH : H.ideal U = Ideal.span {h}) (hh : IsSMulRegular Γ(X, U.1) h) (y : blowUp Z)
    (hy : blowUpToBase Z y ∈ U.1) :
    ∃ W : (blowUp Z).affineOpens, y ∈ W.1 ∧ ∃ e g : Γ(blowUp Z, W.1),
      (Z.comap (blowUpToBase Z)).ideal W = Ideal.span {e} ∧
      (H.comap (blowUpToBase Z)).ideal W = Ideal.span {e * g} ∧
      IsSMulRegular (Γ(blowUp Z, W.1) ⧸ Ideal.span {g}) e ∧ IsSMulRegular Γ(blowUp Z, W.1) g := by
  have hZU : Z.ideal U = Ideal.span (Set.range ![(1 : Γ(X, U.1))]) := by
    rw [ideal_eq_top_of_subset_compl_support Z U hUZ, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Ideal.span_singleton_one]
  have hcov := iSup_blowUpChartOpen_eq_preimage Z U _ hZU
  have hy' : y ∈ blowUpToBase Z ⁻¹ᵁ U.1 := hy
  rw [← hcov] at hy'
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hy'
  set a := generatorSection Z U _ hZU m
  have ha : (a : Γ(X, U.1)) = 1 := by
    change ![(1 : Γ(X, U.1))] m = 1
    rw [Subsingleton.elim m 0]
    rfl
  refine ⟨blowUpChartOpen Z U a, hm, (blowUpChartMap Z U a).hom (a : Γ(X, U.1)),
    (blowUpChartMap Z U a).hom h, ideal_exceptionalIdeal_blowUpChartOpen Z U a, ?_, ?_, ?_⟩
  · rw [ideal_comap_blowUpToBase_blowUpChartOpen, hH, Ideal.map_span, Set.image_singleton, ha,
      map_one, one_mul]
  · rw [ha, map_one]
    exact IsSMulRegular.one _
  · let Θ : Γ(blowUp Z, (blowUpChartOpen Z U a).1) →+* Localization.Away (a : Γ(X, U.1)) :=
      (Subalgebra.val _).toRingHom.comp (blowUpChartRingIso Z U a).hom.hom
    have hΘ : Function.Injective Θ := Subtype.val_injective.comp
      (blowUpChartRingIso Z U a).commRingCatIsoToRingEquiv.injective
    refine isSMulRegular_of_injective Θ hΘ ?_
    have : Θ ((blowUpChartMap Z U a).hom h) =
        algebraMap Γ(X, U.1) (Localization.Away (a : Γ(X, U.1))) h := by
      change Subtype.val ((blowUpChartRingIso Z U a).hom.hom ((blowUpChartMap Z U a).hom h)) = _
      rw [AlgebraicGeometry.blowUpChartRingIso_hom_blowUpChartMap]
      rfl
    rw [this]
    have : Module.Flat Γ(X, U.1) (Localization.Away (a : Γ(X, U.1))) :=
      IsLocalization.flat _ (Submonoid.powers (a : Γ(X, U.1)))
    exact hh.of_flat

/-- The quotient of `𝒪_{X,p}` by the stalk of a closed subscheme `D` smooth over `k` is formally
smooth over the stalk of the base. -/
private theorem formallySmooth_quotient_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData) [Smooth (D.subschemeι ≫ f)]
    (d : D.subscheme) :
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
      rw [Scheme.Hom.smoothLocus_eq_top]; trivial
    exact this
  let e : (X.presheaf.stalk (D.subschemeι d) ⧸
      AlgebraicGeometry.IdealSheafData.stalk D (D.subschemeι d)) ≃ₐ[
        (Spec (.of k)).presheaf.stalk (f (D.subschemeι d))] D.subscheme.presheaf.stalk d :=
    AlgEquiv.ofRingEquiv (f := MMP.Flips.ResolutionInputs.stalkQuotientEquiv D d) (fun a => by
      change (D.subschemeι.stalkMap d).hom ((f.stalkMap (D.subschemeι d)).hom a) =
        ((D.subschemeι ≫ f).stalkMap d).hom a
      rw [Scheme.Hom.stalkMap_comp]; rfl)
  exact Algebra.FormallySmooth.of_equiv e.symm

/-- If a regular local ring has a regular quotient, the drop in dimension is a natural number. -/
private theorem exists_ringKrullDim_eq_quotient_add {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)] :
    ∃ r : ℕ, ringKrullDim R = ringKrullDim (R ⧸ I) + r := by
  have d1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have d2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)
  have hle := ringKrullDim_quotient_le I
  rw [← d1, ← d2] at hle
  have hle' : Submodule.spanFinrank (IsLocalRing.maximalIdeal (R ⧸ I)) ≤
      Submodule.spanFinrank (IsLocalRing.maximalIdeal R) := by
    exact_mod_cast WithBot.coe_le_coe.mp hle
  refine ⟨Submodule.spanFinrank (IsLocalRing.maximalIdeal R) -
    Submodule.spanFinrank (IsLocalRing.maximalIdeal (R ⧸ I)), ?_⟩
  rw [← d1, ← d2, ← Nat.cast_add, Nat.add_sub_cancel' hle']

open MMP.Flips.ResolutionInputs in
/-- At a point of a closed subscheme smooth over `k`, the quotient of the local ring by the stalk
of the ideal sheaf is regular and formally smooth over the base, of codimension a natural
number. -/
private theorem isRegularLocalRing_and_formallySmooth_quotient_stalk {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (T : X.IdealSheafData)
    (hT : MMP.Mori.IsSmoothScheme (T.subschemeι ≫ sX)) {q : X} (hq : q ∈ T.support) :
    IsRegularLocalRing (X.presheaf.stalk q ⧸ IdealSheafData.stalk T q) ∧
      (letI := (sX.stalkMap q).hom.toAlgebra;
        Algebra.FormallySmooth ((Spec (.of k)).presheaf.stalk (sX q))
          (X.presheaf.stalk q ⧸ IdealSheafData.stalk T q)) ∧
      ∃ r : ℕ, ringKrullDim (X.presheaf.stalk q) =
        ringKrullDim (X.presheaf.stalk q ⧸ IdealSheafData.stalk T q) + r := by
  have hreg := isRegularLocalRing_quotient_stalk sX T hT hq
  have : IsRegularLocalRing (X.presheaf.stalk q) :=
    (smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance q
  refine ⟨hreg, ?_, exists_ringKrullDim_eq_quotient_add _⟩
  obtain ⟨z, rfl⟩ : ∃ z, T.subschemeι z = q := by
    rwa [← SetLike.mem_coe, ← T.range_subschemeι] at hq
  have : Smooth (T.subschemeι ≫ sX) := hT.smooth
  exact formallySmooth_quotient_stalk sX T z

open MMP.Flips.ResolutionInputs in
/-- At a point of a smooth hypersurface `H`, the local ring of `X` has dimension one more than that
of `H`. -/
private theorem ringKrullDim_stalk_eq_quotient_add_one {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] {H : X.IdealSheafData}
    (hH : MMP.Resolution.IsSmoothHypersurface sX H) {q : X} (hq : q ∈ H.support) :
    ringKrullDim (X.presheaf.stalk q) =
      ringKrullDim (X.presheaf.stalk q ⧸ IdealSheafData.stalk H q) + ((1 : ℕ) : WithBot ℕ∞) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hreg := isRegularLocalRing_quotient_stalk sX H hH.1 hq
  have : IsRegularLocalRing (X.presheaf.stalk q) :=
    (smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance q
  have : IsDomain (X.presheaf.stalk q ⧸ IdealSheafData.stalk H q) :=
    IsRegularLocalRing.isDomain _
  have : (IdealSheafData.stalk H q).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hht := height_stalk_eq_one_of_isPureCodimOne H hH.2 (x := q)
  rw [← ringKrullDim_quotient_add_one_of_height_eq_one _ hht, Nat.cast_one]

open MMP.Flips.ResolutionInputs MMP.Resolution.Bridges in
/-- **A good chart over the centre.** A point of `B_ZX` over `Z` lies in a chart, in coordinates
adapted to the flag `Z ⊆ H ⊆ X`, on which `π^*I_Z = (e)`, `π^*I_H = (e g)`, `e` is a nonzerodivisor
modulo `g` and `g` is a nonzerodivisor. -/
private theorem exists_good_nhd_of_mem_support {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (H Z : X.IdealSheafData) (hH : MMP.Resolution.IsSmoothHypersurface sX H)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZH : H ≤ Z) (y : blowUp Z)
    (hpZ : blowUpToBase Z y ∈ Z.support) :
    ∃ W : (blowUp Z).affineOpens, y ∈ W.1 ∧ ∃ e g : Γ(blowUp Z, W.1),
      (Z.comap (blowUpToBase Z)).ideal W = Ideal.span {e} ∧
      (H.comap (blowUpToBase Z)).ideal W = Ideal.span {e * g} ∧
      IsSMulRegular (Γ(blowUp Z, W.1) ⧸ Ideal.span {g}) e ∧ IsSMulRegular Γ(blowUp Z, W.1) g := by
  classical
  set p := blowUpToBase Z y
  have hpH : p ∈ H.support := Scheme.IdealSheafData.support_antitone hZH hpZ
  obtain ⟨hHreg, -, -⟩ := isRegularLocalRing_and_formallySmooth_quotient_stalk sX H hH.1 hpH
  obtain ⟨hZreg, hZsm, r, hr⟩ := isRegularLocalRing_and_formallySmooth_quotient_stalk sX Z hZ hpZ
  obtain ⟨hrN, U, hU, hpU, x, hx, hcutH, hcutZ⟩ :=
    exists_isLocalCoordinates_isCutOutByFirst_of_stalk sX H Z hZH p hHreg hZreg hZsm
      (ringKrullDim_stalk_eq_quotient_add_one sX hH hpH) hr
  let c : MMP.Resolution.BlowupChartData Z :=
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
  have hyU : y ∈ blowUpToBase Z ⁻¹ᵁ c.U := hpU
  rw [← iSup_chart_eq_preimage c] at hyU
  obtain ⟨ℓ, hℓ⟩ := TopologicalSpace.Opens.mem_iSup.mp hyU
  have hH' : H.ideal ⟨c.U, hU⟩ = Ideal.span {c.x ⟨0, ℓ.pos⟩} := by
    rw [hcutH ⟨U, hU⟩ le_rfl]
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [presheaf_map_homOfLE_refl_apply]
      change x i = x (Fin.castLE hrN ⟨0, ℓ.pos⟩)
      congr 1
      ext
      simp only [Fin.val_castLE]
      omega
    · rintro rfl
      refine ⟨Fin.castLE hrN ⟨0, ℓ.pos⟩, by simp, ?_⟩
      rw [presheaf_map_homOfLE_refl_apply]
  obtain ⟨e, g, h1, h2, h3, h4⟩ := exists_good_chart sX H Z c hU x hx hrN (fun _ => rfl) ℓ hH'
  exact ⟨⟨c.chart ℓ, isAffineOpen_chart c hU ℓ⟩, hℓ, e, g, h1, h2, h3, h4⟩

open MMP.Flips.ResolutionInputs MMP.Resolution.Bridges in
/-- **A good chart off the centre, on the hypersurface.** A point of `B_ZX` over a point of `H` off
`Z` lies in an affine open on which `π^*I_Z = (1)` and `π^*I_H = (π^*h)`, `π^*h` a
nonzerodivisor. -/
private theorem exists_good_nhd_of_notMem_of_mem {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (H Z : X.IdealSheafData) (hH : MMP.Resolution.IsSmoothHypersurface sX H) (y : blowUp Z)
    (hpZ : blowUpToBase Z y ∉ Z.support) (hpH : blowUpToBase Z y ∈ H.support) :
    ∃ W : (blowUp Z).affineOpens, y ∈ W.1 ∧ ∃ e g : Γ(blowUp Z, W.1),
      (Z.comap (blowUpToBase Z)).ideal W = Ideal.span {e} ∧
      (H.comap (blowUpToBase Z)).ideal W = Ideal.span {e * g} ∧
      IsSMulRegular (Γ(blowUp Z, W.1) ⧸ Ideal.span {g}) e ∧ IsSMulRegular Γ(blowUp Z, W.1) g := by
  classical
  set p := blowUpToBase Z y
  obtain ⟨hHreg, hHsm, -⟩ := isRegularLocalRing_and_formallySmooth_quotient_stalk sX H hH.1 hpH
  obtain ⟨h1N, U, hU, hpU, x, hx, hcutH, -⟩ :=
    exists_isLocalCoordinates_isCutOutByFirst_of_stalk sX H H le_rfl p hHreg hHreg hHsm
      (ringKrullDim_stalk_eq_quotient_add_one sX hH hpH)
      (ringKrullDim_stalk_eq_quotient_add_one sX hH hpH)
  obtain ⟨f, hfV, hpf⟩ := hU.exists_basicOpen_le (V := Z.support.compl) ⟨p, hpZ⟩ hpU
  let U' : X.affineOpens := ⟨X.basicOpen f, hU.basicOpen f⟩
  have hU'U : X.basicOpen f ≤ U := X.basicOpen_le f
  set h := (X.presheaf.map (homOfLE hU'U).op).hom (x ⟨0, h1N⟩)
  have hH' : H.ideal U' = Ideal.span {h} := by
    rw [hcutH U' hU'U]
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have : i = ⟨0, h1N⟩ := Fin.ext (Nat.lt_one_iff.mp hi)
      rw [this]
    · rintro rfl
      exact ⟨⟨0, h1N⟩, by simp, rfl⟩
  have hh : IsSMulRegular Γ(X, X.basicOpen f) h := by
    have := hU.isLocalization_basicOpen f
    have : Module.Flat Γ(X, U) Γ(X, X.basicOpen f) :=
      IsLocalization.flat _ (Submonoid.powers f)
    exact (isSMulRegular_of_isLocalCoordinates sX hU x hx ⟨0, h1N⟩).of_flat
  exact exists_good_off_centre H Z U' (fun q hq => hfV hq) hH' hh y hpf

open MMP.Flips.ResolutionInputs MMP.Resolution.Bridges in
/-- **Every point of `B_ZX` has a good chart.** In the setting of Kollár 3.87, every point of
`B_ZX` lies in an affine open `W` on which `π^*I_Z = (e)`, `π^*I_H = (e g)`, `e` is a
nonzerodivisor modulo `g` and `g` is a nonzerodivisor. Over a point of `Z` this is the chart
computation in coordinates adapted to the flag `Z ⊆ H ⊆ X`; elsewhere `π` is an isomorphism. -/
private theorem exists_good_nhd {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    (H Z : X.IdealSheafData) (hH : MMP.Resolution.IsSmoothHypersurface sX H)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZH : H ≤ Z) (y : blowUp Z) :
    ∃ W : (blowUp Z).affineOpens, y ∈ W.1 ∧ ∃ e g : Γ(blowUp Z, W.1),
      (Z.comap (blowUpToBase Z)).ideal W = Ideal.span {e} ∧
      (H.comap (blowUpToBase Z)).ideal W = Ideal.span {e * g} ∧
      IsSMulRegular (Γ(blowUp Z, W.1) ⧸ Ideal.span {g}) e ∧ IsSMulRegular Γ(blowUp Z, W.1) g := by
  classical
  have : Smooth sX := hX.smooth
  set p := blowUpToBase Z y
  by_cases hpZ : p ∈ Z.support
  · exact exists_good_nhd_of_mem_support sX H Z hH hZ hZH y hpZ
  by_cases hpH : p ∈ H.support
  · exact exists_good_nhd_of_notMem_of_mem sX H Z hH y hpZ hpH
  obtain ⟨U, hU, hpU, hUH⟩ :=
    exists_isAffineOpen_mem_and_subset (U := H.support.compl) (x := p) hpH
  have hUH' : (U : Set X) ⊆ (H.support : Set X)ᶜ := hUH
  have hUZ : (U : Set X) ⊆ (Z.support : Set X)ᶜ := fun q hq hqZ =>
    hUH' hq (Scheme.IdealSheafData.support_antitone hZH hqZ)
  refine exists_good_off_centre H Z ⟨U, hU⟩ hUZ (h := 1) ?_ (IsSMulRegular.one _) y hpU
  rw [ideal_eq_top_of_subset_compl_support H ⟨U, hU⟩ hUH', Ideal.span_singleton_one]

open Limits in
/-- `B_ZH`, as the closed subscheme of `B_ZX` cut out by the kernel of the canonical lift, is
smooth over `k`. -/
private theorem isSmoothScheme_ker_canonicalLift_subschemeι {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (_hX : MMP.Mori.IsSmoothScheme sX)
    (H Z : X.IdealSheafData) (hHs : MMP.Mori.IsSmoothScheme (H.subschemeι ≫ sX))
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZH : H ≤ Z) :
    MMP.Mori.IsSmoothScheme ((MMP.Resolution.canonicalLift H.subschemeι Z).ker.subschemeι ≫
      blowUpToBase Z ≫ sX) := by
  set f := MMP.Resolution.canonicalLift H.subschemeι Z
  have : IsClosedImmersion f := MMP.Resolution.Bridges.isClosedImmersion_canonicalLift _ Z
  have hsH : Smooth (H.subschemeι ≫ sX) := hHs.smooth
  have hZ' : MMP.Mori.IsSmoothScheme ((Z.comap H.subschemeι).subschemeι ≫ H.subschemeι ≫ sX) := by
    have e : (Z.comap H.subschemeι).subschemeι ≫ H.subschemeι ≫ sX =
        ((Z.comapIso H.subschemeι).hom ≫ pullback.snd H.subschemeι Z.subschemeι) ≫
          Z.subschemeι ≫ sX := by
      rw [← Z.comapIso_hom_fst H.subschemeι, Category.assoc, Category.assoc,
        ← Category.assoc _ H.subschemeι, pullback.condition, Category.assoc]
    rw [e]
    have : IsIso (pullback.snd H.subschemeι Z.subschemeι) := by
      rw [← Scheme.IdealSheafData.inclusion_subschemeι hZH]
      exact pullback_snd_iso_of_right_factors_mono (Scheme.IdealSheafData.inclusion hZH)
        H.subschemeι
    have hsZ : Smooth (Z.subschemeι ≫ sX) := hZ.smooth
    exact MMP.Mori.isSmoothScheme_of_smooth inferInstance
  have hB := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
    (H.subschemeι ≫ sX) (Z.comap H.subschemeι) ⟨hHs, hZ'⟩).1
  have e : f.ker.subschemeι ≫ blowUpToBase Z ≫ sX =
      inv f.toImage ≫ blowUpToBase (Z.comap H.subschemeι) ≫ H.subschemeι ≫ sX := by
    have h1 : f.ker.subschemeι = inv f.toImage ≫ f := by
      rw [IsIso.eq_inv_comp, f.toImage_imageι]
    rw [h1, Category.assoc, ← Category.assoc f, MMP.Resolution.canonicalLift_comp_blowUpToBase,
      Category.assoc]
  rw [e]
  exact MMP.Mori.isSmoothScheme_of_smooth inferInstance

/-- The ideal of `B_ZH ⊆ B_ZX` times `π^*I_Z` is `π^*I_H` (Kollár 3.87): on a good chart
`π^*I_Z = (e)`, `π^*I_H = (e g)` and the ideal of `B_ZH` is `(g)`. -/
private theorem ker_canonicalLift_mul_comap_eq_comap
    {k : Type u} [Field k] [CharZero k] {X : AlgebraicGeometry.Scheme.{u}}
    (sX : X ⟶ AlgebraicGeometry.Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    (H Z : X.IdealSheafData) (hH : MMP.Resolution.IsSmoothHypersurface sX H)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZH : H ≤ Z) :
    (MMP.Resolution.canonicalLift H.subschemeι Z).ker *
          Z.comap (AlgebraicGeometry.blowUpToBase Z) =
        H.comap (AlgebraicGeometry.blowUpToBase Z) := by
  apply AlgebraicGeometry.IdealSheafData.eq_of_stalk_eq
  intro y
  obtain ⟨W, hyW, e, g, hE, hK, hreg, -⟩ := exists_good_nhd sX hX H Z hH hZ hZH y
  have hJ := ideal_ker_canonicalLift_eq_span H Z W hE hK hreg
  rw [IdealSheafData.stalk_mul, IdealSheafData.stalk_eq_map_germ _ y W hyW,
    IdealSheafData.stalk_eq_map_germ _ y W hyW, IdealSheafData.stalk_eq_map_germ _ y W hyW,
    hJ, hE, hK, ← Ideal.map_mul, Ideal.span_singleton_mul_span_singleton, mul_comm]

/-- A point of a closed subscheme lying over the generic point of an irreducible component of its
support is maximal for specialization. -/
private theorem isMax_of_subschemeι_eq_irreducibleSetEquivPoints {P : Scheme.{u}}
    (D : P.IdealSheafData) {W : TopologicalSpace.IrreducibleCloseds P}
    (hW : Maximal (fun W' : TopologicalSpace.IrreducibleCloseds P ↦ (W' : Set P) ⊆ D.support) W)
    {z : D.subscheme} (hz : D.subschemeι z = irreducibleSetEquivPoints W) : IsMax z := by
  set e := irreducibleSetEquivPoints (α := P)
  intro b hb
  rw [Scheme.le_iff_specializes] at hb ⊢
  have hb' : D.subschemeι b ⤳ e W := hz ▸ hb.map D.subschemeι.continuous
  have hbD : D.subschemeι b ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]
    exact ⟨b, rfl⟩
  have hle : W ≤ e.symm (D.subschemeι b) := by
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
    exact hb'
  have hsub : ((e.symm (D.subschemeι b) : TopologicalSpace.IrreducibleCloseds P) :
      Set P) ⊆ D.support := by
    change closure {D.subschemeι b} ⊆ _
    exact closure_minimal (Set.singleton_subset_iff.mpr hbD) D.support.isClosed
  have hge := hW.2 hsub hle
  rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes, ← hz] at hge
  exact D.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp hge

/-- If an ideal sheaf `D` is generated on an affine open `V` by a nonzerodivisor `g`, the local
ring of `P` at a point of `D.subscheme` over `V` has dimension one more than that of
`D.subscheme`. -/
private theorem ringKrullDim_stalk_subschemeι_eq_add_one {P : Scheme.{u}} [IsLocallyNoetherian P]
    (D : P.IdealSheafData) (V : P.affineOpens) {g : Γ(P, V.1)} (hJ : D.ideal V = Ideal.span {g})
    (hg : IsSMulRegular Γ(P, V.1) g) (z : D.subscheme) (hηV : D.subschemeι z ∈ V.1) :
    ringKrullDim (P.presheaf.stalk (D.subschemeι z)) =
      ringKrullDim (D.subscheme.presheaf.stalk z) + 1 := by
  set η := D.subschemeι z
  have hzD : η ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]
    exact ⟨z, rfl⟩
  have hst : IdealSheafData.stalk D η = Ideal.span {(P.presheaf.germ V.1 η hηV).hom g} := by
    rw [IdealSheafData.stalk_eq_map_germ D η V hηV, hJ, Ideal.map_span, Set.image_singleton]
  let _ : Algebra Γ(P, V.1) (P.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk P.presheaf ⟨η, hηV⟩
  have : IsLocalization.AtPrime (P.presheaf.stalk η) (V.2.primeIdealOf ⟨η, hηV⟩).asIdeal :=
    V.2.isLocalization_stalk ⟨η, hηV⟩
  have : Module.Flat Γ(P, V.1) (P.presheaf.stalk η) :=
    IsLocalization.flat _ (V.2.primeIdealOf ⟨η, hηV⟩).asIdeal.primeCompl
  have hgreg : IsSMulRegular (P.presheaf.stalk η) ((P.presheaf.germ V.1 η hηV).hom g) :=
    hg.of_flat
  have hgm : (P.presheaf.germ V.1 η hηV).hom g ∈ IsLocalRing.maximalIdeal (P.presheaf.stalk η) := by
    have hmem := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := D) (U := V) hηV).mp hzD
    rw [Scheme.mem_zeroLocus_iff] at hmem
    have hnot := hmem g (by rw [SetLike.mem_coe, hJ]; exact Ideal.mem_span_singleton_self g)
    rwa [Scheme.mem_basicOpen _ _ _ hηV] at hnot
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hgreg hgm
  rw [← hst, ringKrullDim_eq_of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv D z)]
    at hdim
  exact hdim.symm

/-- The support of the ideal of `B_ZH ⊆ B_ZX` has pure codimension one: at the generic point of
a component it is generated by the nonzerodivisor `g` of a good chart, so the local ring there
has dimension one (Kollár 3.87). -/
private theorem isPureCodimOne_support_ker_canonicalLift
    {k : Type u} [Field k] [CharZero k] {X : AlgebraicGeometry.Scheme.{u}}
    (sX : X ⟶ AlgebraicGeometry.Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    (H Z : X.IdealSheafData) (hH : MMP.Resolution.IsSmoothHypersurface sX H)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZH : H ≤ Z) :
    MMP.Mori.IsPureCodimOne (MMP.Resolution.canonicalLift H.subschemeι Z).ker.support := by
  set D := (MMP.Resolution.canonicalLift H.subschemeι Z).ker
  have hBsm : Smooth (blowUpToBase Z ≫ sX) :=
    (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX Z
      ⟨hX, hZ⟩).1
  have : LocallyOfFiniteType (blowUpToBase Z ≫ sX) :=
    instLocallyOfFiniteTypeOfLocallyOfFinitePresentation _
      (hf := instLocallyOfFinitePresentationOfSmooth _)
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z ≫ sX)
  intro W hW
  set e := irreducibleSetEquivPoints (α := blowUp Z)
  have hWη : (W : Set (blowUp Z)) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set (blowUp Z)) := by
    rw [hWη]
    exact subset_closure rfl
  have hηD : e W ∈ D.support := hW.1 hηW
  obtain ⟨z, hz⟩ : ∃ z, D.subschemeι z = e W := by
    rwa [← SetLike.mem_coe, ← D.range_subschemeι] at hηD
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1, ← hz]
  have hz0 : ringKrullDim (D.subscheme.presheaf.stalk z) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight,
      Order.coheight_eq_zero.mpr (isMax_of_subschemeι_eq_irreducibleSetEquivPoints D hW hz)]
    rfl
  obtain ⟨V, hηV, a, g, hE, hK, hreg, hg⟩ := exists_good_nhd sX hX H Z hH hZ hZH (D.subschemeι z)
  have hdim := ringKrullDim_stalk_subschemeι_eq_add_one D V
    (ideal_ker_canonicalLift_eq_span H Z V hE hK hreg) hg z hηV
  rw [hz0, zero_add, ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim

/-- Let `X` be smooth over a field `k` of characteristic `0`, `H ⊆ X` a smooth hypersurface
and `Z ⊆ H` a smooth closed subscheme. Then the canonical lift `B_ZH → B_ZX` of `H ↪ X` is a
closed immersion, its ideal sheaf `I` satisfies `I · π^*I_Z = π^*I_H` (that is,
`I = 𝒪_{B_ZX}(F)·π^*𝒪_X(-H)`), and it is a smooth hypersurface of `B_ZX`. -/
@[mmp "lem_kr3d_transform_of_hypersurface_containing_center"]
public theorem ker_canonicalLift_subschemeι_mul_comap_eq_comap
    {k : Type u} [Field k] [CharZero k] {X : AlgebraicGeometry.Scheme.{u}}
    (sX : X ⟶ AlgebraicGeometry.Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    (H Z : X.IdealSheafData) (hH : MMP.Resolution.IsSmoothHypersurface sX H)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZH : H ≤ Z) :
    AlgebraicGeometry.IsClosedImmersion
        (MMP.Resolution.canonicalLift H.subschemeι Z) ∧
      (MMP.Resolution.canonicalLift H.subschemeι Z).ker *
          Z.comap (AlgebraicGeometry.blowUpToBase Z) =
        H.comap (AlgebraicGeometry.blowUpToBase Z) ∧
      MMP.Resolution.IsSmoothHypersurface (AlgebraicGeometry.blowUpToBase Z ≫ sX)
        (MMP.Resolution.canonicalLift H.subschemeι Z).ker :=
  ⟨MMP.Resolution.Bridges.isClosedImmersion_canonicalLift H.subschemeι Z,
    ker_canonicalLift_mul_comap_eq_comap sX hX H Z hH hZ hZH,
    ⟨isSmoothScheme_ker_canonicalLift_subschemeι sX hX H Z hH.1 hZ hZH,
      isPureCodimOne_support_ker_canonicalLift sX hX H Z hH hZ hZH⟩⟩

end MMP.Resolution
