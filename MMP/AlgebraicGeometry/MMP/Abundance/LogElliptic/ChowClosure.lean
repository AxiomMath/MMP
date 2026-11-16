module

public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree
import MMP.AlgebraicGeometry.Intersection.ChowVarietyFixedDegree
import MMP.AlgebraicGeometry.Intersection.PairingSeparation

/-!
# The Chow closure of the elliptic fibration exists and has a surface as base

Let `(X, Δ_X)` satisfy the assumptions of FA 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`),
with `f_U : U ⟶ Z` a log elliptic fiber space on a nonempty open `U ⊆ X` as in (15.4.3). Then
`f_U` has a Chow closure `(Z₀, Z̄, Ū)` (`MMP.Flips.IsChowClosure`): the reduced closure, in the
normalized Chow variety of curves of fixed degree in `X`, of the family of fibres of `f_U` over a
dense open `Z₀ ⊆ Z`. Moreover, for every Chow closure the base `Z̄` is a surface: it contains the
open `Z₀` of `Z`, and `Z` has dimension `3 - 1 = 2` since the generic fibre of `f_U` is a curve.

The construction. Embed `X` in `ℙᴺ_k`. Over a dense open `Z₁ ⊆ Z` the morphism `f_U` is smooth,
its fibres are curves, and the curves in its closed fibres are `(K_X + Δ_X)`-trivial. The fibres
of `f_U` over `Z₁` form a proper flat family of curves of a fixed degree `d` in `X`, so they are
classified by a morphism `φ : Z₁ ⟶ 𝒞_d(X)` to the Chow variety of degree-`d` curve cycles.
Distinct closed fibres are disjoint, so `φ` is injective on closed points and `Z₁` is
quasi-finite over the reduced closure `W` of the image of `φ`. The normalization `Z̄` of `W` in
`Z₁` is finite over `W`, normal and projective, and contains `Z₁` as an open subscheme by
Zariski's main theorem. The support incidence `Ū ⊆ Z̄ ×ₖ X` of `Z̄ ⟶ 𝒞_d(X)` restricts over `Z₁`
to the graph of `f_U`; it is integral since each of its components dominates `Z̄`. Its fibres
over closed points are the supports of the cycles of `𝒞_d(X)`: the degree of
`𝒪_X(m(K_X + Δ_X))` on these cycles is constant on the connected image of `Z̄`, hence zero, and
nefness makes every curve on them `(K_X + Δ_X)`-trivial; a fixed curve contains the supports of
only finitely many degree-`d` cycles. Over `Z₁` the projection `Ū ⟶ Z̄` is `f_U`, so its generic
fibre has global sections the function field of `Z̄`, and Zariski's connectedness theorem over
the normal base `Z̄` gives connected fibres. The fibres are curves: their components have
dimension at least `dim Ū - dim Z̄ = 1`, at most one over closed points, and at most one
everywhere by upper semicontinuity of fibre dimension.

## Main results

* `MMP.Flips.exists_isChowClosure_and_dim_eq_two`: a Chow closure of `f_U` exists, and every
  Chow closure `(Z₀, Z̄, Ū)` of `f_U` has `dim Z̄ = 2`.

## Implementation notes

The source works over `ℂ`; the statement is made over any algebraically closed field `k` of
characteristic zero. A Chow closure is the datum `(Z₀, Z̄, s_{Z̄}, j, Ū)` of
`MMP.Flips.IsChowClosure`: the open `Z₀ ⊆ Z`, the scheme `Z̄` over `k`, the open immersion
`j : Z₀ ⟶ Z̄` over `k`, and the ideal sheaf of `Ū` in `Z̄ ×_k X`. The dimension of `Z̄` is its
`topologicalKrullDim`.

The Chow variety `𝒞_d(X)` of curves of degree `d` on `X ⊆ ℙᴺ_k` is
`MMP.Chow.exists_chowVariety`. Its degree constancy is stated for `ℚ`-Cartier divisors; on the
integral scheme `X` every invertible sheaf is isomorphic to the sheaf of a Cartier divisor, and
the degree on a cycle only depends on the sheaf up to isomorphism, so the constancy holds for
every invertible sheaf on `X`, in particular for `𝒪_X(m(K_X + Δ_X))`.

`Z̄` is taken to be the normalization of `W` in `Z₁` rather than the normalization of `W`: then
`Z₁ ⟶ Z̄` is birational by construction, and no argument on separable degrees is needed.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], proof of 15.10
* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3–I.4
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace MMP.Flips

open MMP.Mori

section Construction

open Stacks.AlgebraicGeometry.ProjPolyChart

/-- The fundamental cycle `∑ᵢ mᵢ r_*[Cᵢ]` of the fibre over `s` of a family `ρ : 𝒟 ⟶ T`, pushed
forward along `r : 𝒟 ⟶ X`. -/
private noncomputable abbrev fibreCycle {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {T 𝒟 : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (ρ : 𝒟 ⟶ T)
    (r : 𝒟 ⟶ X) (s : T) : Mori.OneCycle ℤ sX :=
  ∑ᶠ C : {C : Mori.ProperCurve (ρ.fiberι s ≫ ρ ≫ sT) //
          closure {C.point} ∈ irreducibleComponents (ρ.fiber s)},
    ((Module.length ((ρ.fiber s).presheaf.stalk C.1.point)
        ((ρ.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
      Mori.cyclePushforwardOfPoint ℤ sX (ρ.fiberι s ≫ r) C.1.point

/-- The support `⋃ᵢ Cᵢ` of a 1-cycle `∑ᵢ mᵢ Cᵢ`. -/
private abbrev cycleSupport {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (Z : Mori.OneCycle ℤ sX) : Set X :=
  ⋃ C ∈ Z.support, closure {C.point}

/-- The `𝒪(1)`-degree of a 1-cycle on `X ⊆ ℙᴺ_k`, computed on its push-forward to `ℙᴺ_k`. -/
private noncomputable abbrev projDegree {k : Type u} [Field k] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    (Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)) : ℤ :=
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
    (Mori.OneCycle.pushforward ℤ (i ≫ projToSpecCoeff k N) (projToSpecCoeff k N) i Z)

/-- **The Chow variety of curves of degree `d`** on an integral `X ⊆ ℙᴺ_k`, with the degree of
every invertible sheaf on `X` constant on its connected components. -/
private theorem exists_chowVariety_of_isIntegral{k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] {N : ℕ} (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) :
    ∃ (𝒞 : Scheme.{u}) (s𝒞 : 𝒞 ⟶ Spec (.of k))
      (cycOf : 𝒞 → Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)),
      IsProjectiveMorphism s𝒞 ∧ IsReduced 𝒞 ∧
      Set.BijOn cycOf {c | IsClosed ({c} : Set 𝒞)} {Z | 0 ≤ Z ∧ projDegree i Z = d} ∧
      (∀ (S 𝒞' : Scheme.{u}) (sS : S ⟶ Spec (.of k)), Mori.IsNormalVariety k sS →
        ∀ (π : 𝒞' ⟶ S) (q : 𝒞' ⟶ X) (hπq : π ≫ sS = q ≫ i ≫ projToSpecCoeff k N),
          IsClosedImmersion (pullback.lift π q hπq) → IsProper π → Flat π →
          (∀ s : S, IsClosed ({s} : Set S) → ∀ x : π.fiber s,
            closure {x} ∈ irreducibleComponents (π.fiber s) →
              topologicalKrullDim (Mori.curveSubschemeAt x) = 1) →
          (∀ s : S, IsClosed ({s} : Set S) →
            projDegree i (fibreCycle (i ≫ projToSpecCoeff k N) sS π q s) = d) →
          ∃ φ : S ⟶ 𝒞, φ ≫ s𝒞 = sS ∧
            ∀ s : S, IsClosed ({s} : Set S) →
              cycOf (φ s) = fibreCycle (i ≫ projToSpecCoeff k N) sS π q s) ∧
      (∀ (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)), Mori.IsNormalVariety k sS →
        ∀ φ : S ⟶ 𝒞, φ ≫ s𝒞 = sS →
          ∃ I : Set (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}), IsClosed I ∧
            (∀ p : (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}), IsClosed {p} →
              (p ∈ I ↔ pullback.snd sS (i ≫ projToSpecCoeff k N) p ∈
                cycleSupport (cycOf (φ (pullback.fst sS (i ≫ projToSpecCoeff k N) p))))) ∧
            ∀ Z, Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Z →
              Dense (pullback.fst sS (i ≫ projToSpecCoeff k N) '' Z)) ∧
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        ∀ c c' : 𝒞, IsClosed ({c} : Set 𝒞) →
        IsClosed ({c'} : Set 𝒞) → c' ∈ connectedComponent c →
          Mori.OneCycle.degree ℤ (i ≫ projToSpecCoeff k N) L (cycOf c) =
            Mori.OneCycle.degree ℤ (i ≫ projToSpecCoeff k N) L (cycOf c') := by
  obtain ⟨𝒞, s𝒞, cycOf, h₁, h₂, h₃, h₄, h₅, h₆⟩ := MMP.Chow.exists_chowVariety i d hd
  refine ⟨𝒞, s𝒞, cycOf, h₁, h₂, h₃, h₄, h₅, fun L _ c c' hc hc' hcc => ?_⟩
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have hE : Fourfold.KCartierDivisor.toReal (KCartierDivisor.ofCartier ℚ E) =
      KCartierDivisor.ofCartier ℝ E := by
    simp [Fourfold.KCartierDivisor.toReal, KCartierDivisor.ofCartier]
  have h := h₆ (KCartierDivisor.ofCartier ℚ E) c c' hc hc' hcc
  rw [hE, OneCycle.intersectionNumber_ofCartier, OneCycle.intersectionNumber_ofCartier,
    MMP.Chow.FixedDegreeCurveCyclesProof.cartierDegree_mapRange_cast,
    MMP.Chow.FixedDegreeCurveCyclesProof.cartierDegree_mapRange_cast] at h
  have hL : ∀ Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N),
      Mori.OneCycle.degree ℤ (i ≫ projToSpecCoeff k N) L Z =
        Mori.OneCycle.degree ℤ (i ≫ projToSpecCoeff k N)
          (MMP.CartierDivisor.sheaf E) Z := fun Z => by
    rw [Mori.OneCycle.degree_apply, Mori.OneCycle.degree_apply]
    exact Finsupp.sum_congr fun C _ => by
      rw [show C.degree k L = C.degree k (MMP.CartierDivisor.sheaf E) from
        degreeOn_eq_of_iso k _ C.ι C.dim_le e]
  rw [hL, hL]
  exact_mod_cast h

/-- The `𝒪(1)`-degree of a nonzero effective 1-cycle on `X ⊆ ℙᴺ_k` is positive. -/
private theorem projDegree_pos {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i]
    {Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)} (hZ : 0 ≤ Z) (hZ0 : Z ≠ 0) :
    0 < projDegree i Z := by
  set Wp := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z
  have hWnn : ∀ C, 0 ≤ Wp C :=
    MMP.Chow.FixedDegreeCurveCyclesProof.pushforward_nonneg i _ hZ
  obtain ⟨C, hC⟩ : Wp.support.Nonempty := Finsupp.support_nonempty_iff.mpr fun h0 =>
    hZ0 (MMP.Chow.FixedDegreeCurveCyclesProof.pushforward_injective i _
      (by rwa [map_zero]))
  simp only [projDegree]
  erw [Mori.OneCycle.degree_apply, Finsupp.sum]
  exact Finset.sum_pos' (fun C' _ => mul_nonneg (hWnn C')
    (MMP.Chow.DeterminantCurveForm.curveDeg_pos C').le) ⟨C, hC, mul_pos
      (lt_of_le_of_ne (hWnn C) (Ne.symm (Finsupp.mem_support_iff.mp hC)))
      (MMP.Chow.DeterminantCurveForm.curveDeg_pos C)⟩

/-- The reduced induced closed subscheme on an irreducible closed set is irreducible. -/
private theorem irreducibleSpace_subscheme_vanishingIdeal {Y : Scheme.{u}}
    (Z : TopologicalSpace.Closeds Y) (hZ : IsIrreducible (Z : Set Y)) :
    IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  haveI : IrreducibleSpace (Z : Set Y) := Subtype.irreducibleSpace hZ
  exact ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isClosedEmbedding.isEmbedding
    |>.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm.irreducibleSpace_iff.mp
    inferInstance

/-- A nonempty irreducible open subscheme of an irreducible scheme locally of finite type over a
field has the dimension of the ambient scheme. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IrreducibleSpace X]
    (j : Y ⟶ X) [IsOpenImmersion j] [IrreducibleSpace Y] :
    topologicalKrullDim Y = topologicalKrullDim X := by
  have h := ProjectiveSpaceOfModule.topologicalKrullDim_closure_image_of_isOpenImmersion k sX j
    isClosed_univ (IrreducibleSpace.isIrreducible_univ Y)
  have hd : closure (j.base '' Set.univ) = Set.univ := by
    rw [Set.image_univ]
    obtain ⟨y, -⟩ := (IrreducibleSpace.isIrreducible_univ Y).nonempty
    exact (j.isOpenEmbedding.isOpen_range.dense ⟨_, Set.mem_range_self y⟩).closure_eq
  rw [hd, topologicalKrullDim_univ, topologicalKrullDim_univ] at h
  exact h.symm

/-- `3 = 1 + a` forces `a = 2` in `WithBot ℕ∞`. -/
private theorem eq_two_of_three_eq_one_add {a : WithBot ℕ∞} (h1 : (3 : WithBot ℕ∞) = 1 + a) :
    a = 2 := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h1
  | coe b =>
    have h2 : (3 : ℕ∞) = 1 + b := WithBot.coe_injective (by rwa [WithBot.coe_add])
    induction b using ENat.recTopCoe with
    | top => exact absurd h2 (by decide)
    | coe n =>
      have h3 : (3 : ℕ) = 1 + n := by exact_mod_cast h2
      obtain rfl : n = 2 := by omega
      rfl

/-- The base of a log elliptic fiber space on a nonempty open subset of a threefold is a surface:
`dim U = dim (generic fibre) + dim Z = 1 + dim Z`. -/
private theorem topologicalKrullDim_base_eq_two {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {K : Divisor X} {Δ : QDivisor X}
    (hdX : topologicalKrullDim X = 3)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3 (DivisorWithCoeffs.restrict U.ι K)
      (DivisorWithCoeffs.restrict U.ι Δ) fU) :
    topologicalKrullDim Z = 2 := by
  have hZ := hfU.isContraction.isVariety_target
  have := hZ.toIsIntegral
  have := hZ.toLocallyOfFiniteType
  have : Nonempty U := ⟨⟨hU.some, hU.some_mem⟩⟩
  have hdU : topologicalKrullDim U = 3 :=
    (topologicalKrullDim_eq_of_isOpenImmersion sX U.ι).trans hdX
  have hfib := hfU.dim_genericFiber
  obtain ⟨x, hx⟩ : ∃ x : U, fU x = genericPoint Z := by
    by_contra hne
    push Not at hne
    have : IsEmpty (fU.base ⁻¹' {genericPoint Z}) := ⟨fun ⟨y, hy⟩ => hne y hy⟩
    have : IsEmpty (TopologicalSpace.IrreducibleCloseds (fU.base ⁻¹' {genericPoint Z})) :=
      ⟨fun s => isEmptyElim s.isIrreducible.nonempty.some⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot] at hfib
    exact WithBot.bot_ne_coe hfib
  rw [← (fU.fiberHomeo (genericPoint Z)).isHomeomorph.topologicalKrullDim_eq] at hfib
  have hgen : fU (genericPoint U) = genericPoint Z := by
    have hsp : fU (genericPoint U) ⤳ genericPoint Z :=
      hx ▸ ((genericPoint_spec U).specializes (Set.mem_univ x)).map fU.continuous
    refine (isGenericPoint_iff_specializes.mpr fun z => ?_).eq (genericPoint_spec Z)
    simp only [Set.mem_univ, iff_true]
    exact hsp.trans ((genericPoint_spec Z).specializes (Set.mem_univ z))
  have hcl : closure (Set.range fU.base) = Set.univ :=
    Set.eq_univ_of_univ_subset (by
      rw [← (genericPoint_spec Z).def]
      exact closure_mono (Set.singleton_subset_iff.mpr ⟨x, hx⟩))
  have h1 := topologicalKrullDim_eq_fiber_add_closure_range fU k (U.ι ≫ sX) sZ
    hfU.isContraction.comp_eq
  rw [hgen, hfib, hcl, topologicalKrullDim_univ, hdU] at h1
  exact eq_two_of_three_eq_one_add h1

/-- Every Chow closure has a surface as base: `Z̄` contains the nonempty open `Z₀` of the surface
`Z`. -/
private theorem topologicalKrullDim_eq_two_of_isChowClosure {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    {U : X.Opens} {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {fU : U.toScheme ⟶ Z}
    {Z₀ : Z.Opens} {Zbar : Scheme.{u}} {sZbar : Zbar ⟶ Spec (.of k)} {j : Z₀.toScheme ⟶ Zbar}
    {Ubar : (pullback sZbar sX).IdealSheafData}
    (hc : IsChowClosure (sZ := sZ) (sZbar := sZbar) k sX K Δ fU Z₀ j Ubar) :
    topologicalKrullDim Zbar = 2 := by
  have hZ := hc.isLogEllipticFiberSpace.isContraction.isVariety_target
  have := hZ.toIsIntegral
  have := hZ.toLocallyOfFiniteType
  have hZbar := hc.isNormalVariety.1
  have := hZbar.toIsIntegral
  have := hZbar.toLocallyOfFiniteType
  have := hc.isOpenImmersion
  have : Nonempty Z₀ := ⟨⟨hc.nonempty.some, hc.nonempty.some_mem⟩⟩
  rw [← topologicalKrullDim_eq_of_isOpenImmersion sZbar j,
    topologicalKrullDim_eq_of_isOpenImmersion sZ Z₀.ι]
  exact topologicalKrullDim_base_eq_two sX hc.satisfiesAbundanceAssumptions.dim_eq U
    hc.nonempty_U sZ fU hc.isLogEllipticFiberSpace

/-- A projective `k`-scheme is a closed subscheme of some `ℙᴺ_k = Proj k[T₀, …, T_N]`. -/
private theorem exists_isClosedImmersion_projToSpecCoeff {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (h : IsProjectiveMorphism sX) :
    ∃ (N : ℕ) (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)),
      IsClosedImmersion i ∧ i ≫ projToSpecCoeff k N = sX := by
  obtain ⟨n, i', hi', hcomp⟩ := h
  have hP := MMP.Chow.FixedDegreeCurveCyclesProof.isoPolyGrading_inv_comp_toSpec k n
  refine ⟨n, i' ≫ (MMP.Intersection.ProjSpace.isoProjectiveSpaceOver k n).inv ≫
    (MMP.Intersection.ProjSpace.isoPolyGrading k n).hom, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, ← hP, Iso.hom_inv_id_assoc,
    ← MMP.Intersection.ProjSpace.isoProjectiveSpaceOver_hom_over, Iso.inv_hom_id_assoc, hcomp]

/-- A point of `p` over `s ∈ O` comes from a point of `p ∣_ O` over `s`. -/
private theorem exists_preimage_ι_of_apply_eq {V T : Scheme.{u}} (p : V ⟶ T) (O : T.Opens)
    {v : V} {s : O} (hv : p v = O.ι s) :
    ∃ y : (p ⁻¹ᵁ O).toScheme, (p ⁻¹ᵁ O).ι y = v ∧ (p ∣_ O) y = s := by
  have hvO : v ∈ p ⁻¹ᵁ O := by
    change p v ∈ O
    rw [hv]
    exact s.2
  obtain ⟨y, rfl⟩ : v ∈ Set.range (p ⁻¹ᵁ O).ι := by rwa [Scheme.Opens.range_ι]
  refine ⟨y, rfl, O.ι.isOpenEmbedding.injective ?_⟩
  rwa [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- The points of `p ∣_ O` over `s` are the points of `p` over `s ∈ O`. -/
private theorem range_restrict_preimage {V T : Scheme.{u}} (p : V ⟶ T) (O : T.Opens) (s : O) :
    Set.range (fun x : ((p ∣_ O) ⁻¹' {s} : Set (p ⁻¹ᵁ O).toScheme) => (p ⁻¹ᵁ O).ι x.1) =
      p ⁻¹' {O.ι s} := by
  have hpt : ∀ y : (p ⁻¹ᵁ O).toScheme, p ((p ⁻¹ᵁ O).ι y) = O.ι ((p ∣_ O) y) := fun y => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  ext v
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
    rw [hpt, hy]
  · intro hv
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hv
    obtain ⟨y, rfl, hy⟩ := exists_preimage_ι_of_apply_eq p O hv
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The image in `W` of the fibre of `p ∣_ O` over `s` is the image of the fibre of `p` over
`s ∈ O`. -/
private theorem range_fiberι_restrict_comp {V T W : Scheme.{u}} (p : V ⟶ T) (O : T.Opens)
    (s : O.toScheme) (r : V ⟶ W) :
    Set.range ((p ∣_ O).fiberι s ≫ (p ⁻¹ᵁ O).ι ≫ r) = r '' (p ⁻¹' {O.ι s}) := by
  rw [← range_restrict_preimage p O s, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Scheme.Hom.range_fiberι]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The fibre of `p ∣_ O` over `s` is homeomorphic to the fibre of `p` over `s ∈ O`. -/
private noncomputable def fiberRestrictHomeo {V T : Scheme.{u}} (p : V ⟶ T) (O : T.Opens)
    (s : O) : (p ∣_ O).fiber s ≃ₜ p.fiber (O.ι s) :=
  ((p ∣_ O).fiberHomeo s).trans
    ((((p ⁻¹ᵁ O).ι.isOpenEmbedding.isEmbedding.comp
      Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
      (Homeomorph.setCongr (range_restrict_preimage p O s))).trans (p.fiberHomeo (O.ι s)).symm)

/-- A homeomorphism maps irreducible components to irreducible components. -/
private theorem image_mem_irreducibleComponents_of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) {S : Set A} (hS : S ∈ irreducibleComponents A) :
    e '' S ∈ irreducibleComponents B := by
  refine ⟨hS.1.image e e.continuous.continuousOn, fun T hT hST => ?_⟩
  have h := hS.2 (hT.image e.symm e.symm.continuous.continuousOn) (by
    rw [← e.symm_image_image S]
    exact Set.image_mono hST)
  calc T = e '' (e.symm '' T) := (e.image_symm_image T).symm
    _ ⊆ e '' S := Set.image_mono h

/-- The reduced closed subscheme `{x}⁻` has the dimension of the closure of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt {Y : Scheme.{u}} (x : Y) :
    topologicalKrullDim (curveSubschemeAt x) = topologicalKrullDim (closure ({x} : Set Y)) := by
  refine MMP.Chow.FixedDegreeCurveCyclesProof.topologicalKrullDim_eq_of_range_eq
    (curveSubschemeAtι x).isClosedEmbedding.isEmbedding Topology.IsEmbedding.subtypeVal ?_
  rw [Subtype.range_coe]
  change Set.range (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({x} : Set Y))).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_closure]

/-- If the components of the fibre of `p` over `s ∈ O` are curves, so are those of the fibre of
`p ∣_ O` over `s`. -/
private theorem topologicalKrullDim_curveSubschemeAt_restrict {V T : Scheme.{u}} (p : V ⟶ T)
    (O : T.Opens) (s : O)
    (h : ∀ Y ∈ irreducibleComponents (p.fiber (O.ι s)), topologicalKrullDim Y = 1)
    (x : (p ∣_ O).fiber s) (hx : closure {x} ∈ irreducibleComponents ((p ∣_ O).fiber s)) :
    topologicalKrullDim (Mori.curveSubschemeAt x) = 1 := by
  set e := fiberRestrictHomeo p O s
  have himg : e '' closure {x} = closure {e x} := by
    rw [e.image_closure, Set.image_singleton]
  have hcomp : closure {e x} ∈ irreducibleComponents (p.fiber (O.ι s)) :=
    himg ▸ image_mem_irreducibleComponents_of_homeomorph e hx
  rw [topologicalKrullDim_curveSubschemeAt, ← h _ hcomp]
  refine MMP.Chow.FixedDegreeCurveCyclesProof.topologicalKrullDim_eq_of_range_eq
    (e.isEmbedding.comp Topology.IsEmbedding.subtypeVal) Topology.IsEmbedding.subtypeVal ?_
  rw [Subtype.range_coe, Set.range_comp, Subtype.range_coe, himg]

open Classical in
/-- The coefficient of `D` in `∑_c n_c [g c]`, for `g` injective. -/
private theorem finset_sum_smul_single_apply {ι P : Type*} (A : Finset ι) (g : ι → P)
    (hg : Function.Injective g) (n : ι → ℤ) (D : P) :
    (∑ c ∈ A, n c • (Finsupp.single (g c) (1 : ℤ))) D =
      if h : ∃ c ∈ A, g c = D then n h.choose else 0 := by
  classical
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single h.choose (fun c _ hc => if_neg fun hgc => hc (hg (hgc.trans
      h.choose_spec.2.symm))) (fun hn => absurd h.choose_spec.1 hn), if_pos h.choose_spec.2]
  · exact Finset.sum_eq_zero fun c hc => if_neg fun hgc => h ⟨c, hc, hgc⟩

/-- **The support of a fundamental cycle.** If `ρ` has a fibre over `s` all of whose
irreducible components are curves, embedded in `X` by the closed immersion `m = ρ.fiberι s ≫ r`
over `k`, then the support of the fibre cycle is the image of the fibre. -/
private theorem cycleSupport_fibreCycle {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {T 𝒟 : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (ρ : 𝒟 ⟶ T)
    (r : 𝒟 ⟶ X) (s : T) [IsClosedImmersion (ρ.fiberι s ≫ r)]
    [IsProper (ρ.fiberι s ≫ ρ ≫ sT)] [IsLocallyNoetherian (ρ.fiber s)]
    [CompactSpace (ρ.fiber s)]
    (hcompat : (ρ.fiberι s ≫ r) ≫ sX = ρ.fiberι s ≫ ρ ≫ sT)
    (hdim : ∀ x : ρ.fiber s, closure {x} ∈ irreducibleComponents (ρ.fiber s) →
      topologicalKrullDim (curveSubschemeAt x) = 1) :
    0 ≤ fibreCycle sX sT ρ r s ∧
      cycleSupport (fibreCycle sX sT ρ r s) = Set.range (ρ.fiberι s ≫ r) := by
  classical
  set m := ρ.fiberι s ≫ r with hm
  haveI : IsNoetherian (ρ.fiber s) := {}
  let ι' := {C : Mori.ProperCurve (ρ.fiberι s ≫ ρ ≫ sT) //
    closure ({C.point} : Set (ρ.fiber s)) ∈ irreducibleComponents (ρ.fiber s)}
  haveI : Finite ι' := by
    haveI := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      (α := ρ.fiber s)).to_subtype
    refine Finite.of_injective (fun C : ι' => (⟨_, C.2⟩ : irreducibleComponents (ρ.fiber s)))
      fun C₁ C₂ h => Subtype.ext (Mori.ProperCurve.ext ?_)
    exact (inseparable_iff_closure_eq.mpr (congrArg Subtype.val h)).eq
  letI : Fintype ι' := Fintype.ofFinite _
  have hpc : ∀ C : ι', Mori.IsProperCurve sX (m C.1.point) := fun C => by
    rw [← MMP.Chow.FixedDegreeCurveCyclesProof.isProperCurve_comp_iff, hcompat]
    exact C.1.isProperCurve
  let g : ι' → Mori.ProperCurve sX := fun C => ⟨m C.1.point, hpc C⟩
  have hg : Function.Injective g := fun C₁ C₂ h => Subtype.ext (Mori.ProperCurve.ext
    (m.isClosedEmbedding.injective (congrArg Mori.ProperCurve.point h)))
  let n : ι' → ℤ := fun C => ((Module.length ((ρ.fiber s).presheaf.stalk C.1.point)
    ((ρ.fiber s).presheaf.stalk C.1.point)).toNat : ℤ)
  have hn : ∀ C : ι', 0 < n C := fun C =>
    Int.natCast_pos.mpr (MMP.Chow.FixedDegreeCurveCyclesProof.toNat_length_stalk_pos C.2)
  have hZ : fibreCycle sX sT ρ r s = ∑ C : ι', n C • Finsupp.single (g C) (1 : ℤ) := by
    unfold fibreCycle
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun C _ => ?_
    congr 1
    unfold Mori.cyclePushforwardOfPoint
    rw [dif_pos (hpc C), MMP.Chow.FixedDegreeCurveCyclesProof.residueFieldDegree_eq_one,
      Nat.cast_one]
  have happ := finset_sum_smul_single_apply Finset.univ g hg n
  refine ⟨fun D => ?_, ?_⟩
  · rw [hZ, happ D]
    split_ifs
    exacts [(hn _).le, le_rfl]
  have hsupp : (fibreCycle sX sT ρ r s).support = Finset.univ.image g := by
    ext D
    rw [Finsupp.mem_support_iff, hZ, happ D, Finset.mem_image]
    exact ⟨fun hD => Classical.byContradiction fun hne => hD (dif_neg hne),
      fun hD => (dif_pos hD).trans_ne (hn _).ne'⟩
  -- every point of the fibre lies on a component, whose generic point is a curve of `ι'`
  have hcover : ∀ x : ρ.fiber s, ∃ C : ι', x ∈ closure ({C.1.point} : Set (ρ.fiber s)) := by
    intro x
    obtain ⟨Y, hY, hxY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({x} : Set (ρ.fiber s)) isIrreducible_singleton
    have hYc := isClosed_of_mem_irreducibleComponents Y hY
    have hgen := hY.1.isGenericPoint_genericPoint_closure
    rw [hYc.closure_eq] at hgen
    have hcl : closure ({hY.1.genericPoint} : Set (ρ.fiber s)) = Y := hgen
    have hcomp : closure ({hY.1.genericPoint} : Set (ρ.fiber s)) ∈
        irreducibleComponents (ρ.fiber s) := by rwa [hcl]
    have hξc : Mori.IsProperCurve (ρ.fiberι s ≫ ρ ≫ sT) hY.1.genericPoint :=
      ⟨hdim _ hcomp, inferInstance⟩
    refine ⟨⟨⟨_, hξc⟩, hcomp⟩, ?_⟩
    change x ∈ closure ({hY.1.genericPoint} : Set (ρ.fiber s))
    rw [hcl]
    exact hxY rfl
  rw [cycleSupport, hsupp]
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop,
    Set.mem_range]
  constructor
  · rintro ⟨D, ⟨C, rfl⟩, hy⟩
    exact closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_range_self _))
      m.isClosedEmbedding.isClosed_range hy
  · rintro ⟨x, rfl⟩
    obtain ⟨C, hC⟩ := hcover x
    exact ⟨g C, ⟨C, rfl⟩, specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hC).map m.continuous)⟩

/-- A morphism locally of finite type between Jacobson schemes which is injective on closed
points is locally quasi-finite: over a closed point the fibre is a closed set whose only closed
point is the given one, hence a single point, and the quasi-finite locus is an open set
containing every closed point. -/
private theorem locallyQuasiFinite_of_injOn_closedPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [JacobsonSpace X] [JacobsonSpace Y]
    (hf : ∀ x x' : X, IsClosed ({x} : Set X) → IsClosed ({x'} : Set X) → f x = f x' → x = x') :
    LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  by_contra hne
  have hcne : ((f.quasiFiniteLocus : Set X)ᶜ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    exact hne (SetLike.coe_injective (h.trans TopologicalSpace.Opens.coe_top.symm))
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hcne
    f.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed
  apply hx
  change f.QuasiFiniteAt x
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have hfx : IsClosed ({f x} : Set Y) := f.closePoints_subset_preimage_closedPoints hxc
  have hF : f ⁻¹' {f x} = {x} := by
    refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr rfl)
    have hFc : IsClosed (f ⁻¹' {f x}) := hfx.preimage f.continuous
    rw [← JacobsonSpace.closure_inter_closedPoints hFc]
    refine (closure_mono fun y hy => ?_).trans (IsClosed.closure_eq hxc).le
    exact hf y x hy.2 hxc hy.1
  haveI : Subsingleton (f.fiber (f x)) := by
    refine ⟨fun a b => (f.fiberHomeo (f x)).injective (Subtype.ext ?_)⟩
    have ha := hF.subset ((f.fiberHomeo (f x)) a).2
    have hb := hF.subset ((f.fiberHomeo (f x)) b).2
    exact ha.trans hb.symm
  have huniv : ({f.asFiber x} : Set (f.fiber (f x))) = Set.univ :=
    Set.eq_univ_of_forall fun a => Subsingleton.elim a (f.asFiber x)
  rw [huniv]
  exact isOpen_univ

/-- A finite morphism is quasi-projective: the structure sheaf of its source is relatively ample,
the inverse image of an affine open being affine. -/
private theorem isQuasiProjective_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] :
    IsQuasiProjective f := by
  refine ⟨⟨inferInstance, inferInstance⟩, Stacks.Ample.unitModule X,
    Stacks.Ample.isInvertibleModule_unit X, ?_⟩
  refine (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f
    (Stacks.Ample.unitModule X)).mp ?_
  refine (Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff f).mpr ?_
  intro V hV
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  infer_instance

/-- A scheme finite over a scheme that is H-projective over a field is H-projective over the
field. -/
private theorem isProjectiveMorphism_comp_of_isFinite {k : Type u} [Field k]
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [IsFinite g] (sY : Y ⟶ Spec (.of k))
    (hY : IsProjectiveMorphism sY) : IsProjectiveMorphism (g ≫ sY) := by
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sY
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sY hY.isHQuasiProjective)
  have hg : IsProjectiveMorphism g :=
    isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
      ⟨isHQuasiProjective_of_isQuasiProjective g L hLa (isQuasiProjective_of_isFinite g),
        inferInstance⟩
  exact hg.comp hY

section FA15Helpers

open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
open Stacks.AlgebraicGeometry.ComponentDegrees

/-- The fibre of `p` over a point `t` of an open `U` is the fibre of `p ∣_ U` over `t`. -/
private theorem exists_isPullback_fiber_restrict {V T : Scheme.{u}}
    (p : V ⟶ T) (U : T.Opens) (t : T) (ht : t ∈ U) :
    ∃ (a : p.fiber t ⟶ p ⁻¹ᵁ U) (g' : Spec (T.residueField t) ⟶ U),
      a ≫ (p ⁻¹ᵁ U).ι = p.fiberι t ∧ g' ≫ U.ι = T.fromSpecResidueField t ∧
      IsPullback a (p.fiberToSpecResidueField t) (p ∣_ U) g' := by
  have hr : Set.range (T.fromSpecResidueField t) ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    simpa using ht
  let g' := IsOpenImmersion.lift U.ι (T.fromSpecResidueField t) hr
  have hg : g' ≫ U.ι = T.fromSpecResidueField t := IsOpenImmersion.lift_fac _ _ _
  have hR := (isPullback_morphismRestrict p U).flip
  have hF : IsPullback (p.fiberι t) (p.fiberToSpecResidueField t) p (T.fromSpecResidueField t) :=
    IsPullback.of_hasPullback _ _
  let a := hR.lift (p.fiberι t) (p.fiberToSpecResidueField t ≫ g')
    (by simpa only [Category.assoc, hg] using hF.w)
  have h1 : a ≫ (p ⁻¹ᵁ U).ι = p.fiberι t := hR.lift_fst _ _ _
  refine ⟨a, g', h1, hg, IsPullback.of_right (h₁₂ := (p ⁻¹ᵁ U).ι) (h₂₂ := U.ι) ?_
    (hR.lift_snd _ _ _) hR⟩
  rwa [h1, hg]

/-- The fibre of `p` over a point of an open over which `p` is smooth is smooth over the
residue field. -/
private theorem smooth_fiberToSpecResidueField_of_smooth_restrict {V T : Scheme.{u}}
    (p : V ⟶ T) (U : T.Opens) [Smooth (p ∣_ U)] (t : T) (ht : t ∈ U) :
    Smooth (p.fiberToSpecResidueField t) := by
  obtain ⟨a, g', -, -, hsq⟩ := exists_isPullback_fiber_restrict p U t ht
  exact MorphismProperty.of_isPullback (P := @Smooth) hsq inferInstance

/-- Cancellation in `WithBot ℕ∞` against a finite summand: `a + d = d + 1` forces `a = 1`. -/
private theorem eq_one_of_add_eq_add_one {a d : WithBot ℕ∞} (hb : d ≠ ⊥) (ht : d ≠ ⊤)
    (h : a + d = d + 1) : a = 1 := by
  lift d to ℕ∞ using hb
  lift d to ℕ using (by simpa using ht)
  induction a using WithBot.recBotCoe with
  | bot => exact absurd h (by norm_cast)
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => norm_cast at h
    | coe a =>
      norm_cast at h ⊢
      omega

/-- A morphism smooth over an open `W` of an open `U` of the target is smooth over the image
of `W` in the target. -/
theorem smooth_morphismRestrict_image {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (W : U.toScheme.Opens) [Smooth (f ∣_ U ∣_ W)] : Smooth (f ∣_ U.ι ''ᵁ W) := by
  let e := morphismRestrictRestrict f U W
  have hw : f ∣_ U.ι ''ᵁ W = inv e.hom.left ≫ (f ∣_ U ∣_ W) ≫ e.hom.right := by
    rw [IsIso.eq_inv_comp]
    exact e.hom.w
  rw [hw]
  infer_instance

/-- Step one: a dense open of `W` over which `g` is smooth, with smooth fibres all of whose
irreducible components are curves. The points of `V` over the generic point of `W` have regular
local rings, hence are smooth points of `V`; so the image of the singular locus, closed since `g`
is proper, misses the generic point, and generic smoothness applies over its complement,
intersected with an open over which the fibre dimension is `dim V - dim W = 1`. -/
private theorem exists_dense_open_smooth_restrict
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {V W : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [IsIntegral V] [IsNormal V] [IsLocallyNoetherian V]
    [IsSeparated sV] [LocallyOfFiniteType sV] [QuasiCompact sV]
    [IsIntegral W] [IsSeparated sW] [LocallyOfFiniteType sW] [QuasiCompact sW]
    (g : V ⟶ W) (hg : g ≫ sW = sV) [IsProper g] [Surjective g]
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1) :
    ∃ U : W.Opens, Dense (U : Set W) ∧ Smooth (g ∣_ U) ∧
      ∀ w ∈ U, Smooth (g.fiberToSpecResidueField w) ∧
        ∀ Z ∈ irreducibleComponents (g.fiber w), topologicalKrullDim Z = 1 := by
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : AlgebraicGeometry.IsVariety k sV := AlgebraicGeometry.IsVariety.mk
  have : AlgebraicGeometry.IsVariety k sW := AlgebraicGeometry.IsVariety.mk
  obtain ⟨V', hV'd, hV'⟩ := (MMP.topologicalKrullDim_fiber_of_isDominant k sV sW g hg).2.1
  have hbot : topologicalKrullDim W ≠ ⊥ := Order.krullDim_ne_bot_iff.mpr
    ⟨⟨closure {genericPoint W}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hdimZ : ∀ w ∈ V', ∀ Z ∈ irreducibleComponents (g.fiber w), topologicalKrullDim Z = 1 :=
    fun w hw Z hZ => eq_one_of_add_eq_add_one hbot
      (topologicalKrullDim_ne_top_of_locallyOfFiniteType k sW) ((hV' w hw Z hZ).trans hdim)
  let Z : Set V := (sV.smoothLocus : Set V)ᶜ
  have hZ : IsClosed Z := sV.smoothLocus.isOpen.isClosed_compl
  have hgZ : IsClosed (g '' Z) := g.isClosedMap Z hZ
  have hη : genericPoint W ∉ g '' Z := by
    rintro ⟨z, hz, hgz⟩
    exact hz (((MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField sV).1 z).2
      (isRegularLocalRing_stalk_of_mem_genericFiber sV sW g hg hdim hgz))
  let U₀ : W.Opens := ⟨(g '' Z)ᶜ, hgZ.isOpen_compl⟩ ⊓ V'
  have hηU₀ : genericPoint W ∈ U₀ :=
    ⟨hη, (genericPoint_spec W).mem_open_set_iff V'.isOpen |>.mpr
      (by obtain ⟨u, hu⟩ := hV'd.nonempty; exact ⟨u, trivial, hu⟩)⟩
  obtain ⟨v, hv⟩ := g.surjective (genericPoint W)
  have hvU₀ : v ∈ g ⁻¹ᵁ U₀ := by simpa [hv] using hηU₀
  have : Nonempty U₀ := ⟨⟨_, hηU₀⟩⟩
  have : Nonempty (g ⁻¹ᵁ U₀) := ⟨⟨_, hvU₀⟩⟩
  let : (g ⁻¹ᵁ U₀).toScheme.Over (Spec (.of k)) := ⟨(g ⁻¹ᵁ U₀).ι ≫ sV⟩
  let : U₀.toScheme.Over (Spec (.of k)) := ⟨U₀.ι ≫ sW⟩
  have : (g ∣_ U₀).IsOver (Spec (.of k)) := ⟨by
    change g ∣_ U₀ ≫ U₀.ι ≫ sW = (g ⁻¹ᵁ U₀).ι ≫ sV
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hg]⟩
  have : Smooth ((g ⁻¹ᵁ U₀).toScheme ↘ Spec (.of k)) := by
    change Smooth ((g ⁻¹ᵁ U₀).ι ≫ sV)
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      eq_top_iff]
    rintro x -
    by_contra hx
    exact x.2.1 ⟨x.1, hx, rfl⟩
  have : LocallyOfFiniteType ((g ⁻¹ᵁ U₀).toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType ((g ⁻¹ᵁ U₀).ι ≫ sV))
  have : QuasiCompact ((g ⁻¹ᵁ U₀).toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact ((g ⁻¹ᵁ U₀).ι ≫ sV))
  have : LocallyOfFiniteType (U₀.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (U₀.ι ≫ sW))
  have : QuasiCompact (U₀.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (U₀.ι ≫ sW))
  obtain ⟨U, hUd, -, hsm, -⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := k) (g ∣_ U₀)
  have hsm' := @smooth_morphismRestrict_image _ _ g U₀ U hsm
  refine ⟨U₀.ι ''ᵁ U, ?_, hsm', fun w hw => ?_⟩
  · obtain ⟨u, hu⟩ := hUd.nonempty
    exact (U₀.ι ''ᵁ U).isOpen.dense ⟨_, ⟨u, hu, rfl⟩⟩
  · refine ⟨smooth_fiberToSpecResidueField_of_smooth_restrict g _ w hw, hdimZ w ?_⟩
    obtain ⟨u, -, rfl⟩ := hw
    exact u.2.2

/-- If the generic fibre of a surjective morphism `g : V ⟶ W` of integral schemes of finite type
over `k` is a curve, then `dim V = dim W + 1`. -/
private theorem topologicalKrullDim_eq_add_one {k : Type u} [Field k] {V W : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k)) [IsIntegral V] [IsIntegral W]
    [LocallyOfFiniteType sV] [LocallyOfFiniteType sW] [CompactSpace W] (g : V ⟶ W)
    (hg : g ≫ sW = sV) (hs : Function.Surjective g)
    (h1 : topologicalKrullDim (g.base ⁻¹' {genericPoint W}) = 1) :
    topologicalKrullDim V = topologicalKrullDim W + 1 := by
  have := locallyOfFiniteType_of_comp_eq sV sW g hg
  have hθ := genericPoint_map_of_surjective g hs
  rw [← (g.fiberHomeo (genericPoint W)).isHomeomorph.topologicalKrullDim_eq] at h1
  have dF := toENat_trdeg_eq_topologicalKrullDim_fiber g (genericPoint V)
    (isGenericPoint_asFiber_genericPoint g)
  have dV := topologicalKrullDim_eq_trdeg_residueField k V sV (genericPoint V)
    (genericPoint_spec V)
  have dW := topologicalKrullDim_eq_trdeg_residueField k W sW (g (genericPoint V))
    (hθ ▸ genericPoint_spec W)
  have ht := congrArg Cardinal.toENat (trdeg_residueField_add sV sW g hg (genericPoint V))
  rw [map_add] at ht
  rw [← hθ, ← dF] at h1
  rw [dV, dW, ← ht, ← h1]
  rfl

/-- In a quasi-sober `T₀` space, every point `p` of a closed set `F` is a specialization of a
point `q ∈ F` with no proper generization in `F`: the generic point of an irreducible component
of `F` containing `p`. -/
private theorem exists_maximal_generization {T : Type*} [TopologicalSpace T] [QuasiSober T]
    [T0Space T] {F : Set T} (hF : IsClosed F) {p : T} (hp : p ∈ F) :
    ∃ q ∈ F, q ⤳ p ∧ ∀ y ∈ F, y ⤳ q → y = q := by
  have : QuasiSober F := hF.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨Y, hY, hpY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({⟨p, hp⟩} : Set F)) isIrreducible_singleton.closure
  have hYc := isClosed_of_mem_irreducibleComponents Y hY
  have hgen := hY.1.isGenericPoint_genericPoint_closure
  rw [hYc.closure_eq] at hgen
  set q' := hY.1.genericPoint
  have hind : Topology.IsInducing ((↑) : F → T) := Topology.IsInducing.subtypeVal
  refine ⟨q'.1, q'.2, ?_, fun y hy hyq => ?_⟩
  · have : q' ⤳ ⟨p, hp⟩ := hgen.specializes (hpY (subset_closure rfl))
    exact this.map continuous_subtype_val
  · have hyq' : (⟨y, hy⟩ : F) ⤳ q' := hind.specializes_iff.mp hyq
    have hsub : Y ⊆ closure ({⟨y, hy⟩} : Set F) := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hyq'))
        isClosed_closure
    have hle := hY.2 isIrreducible_singleton.closure hsub
    have hqy : q' ⤳ ⟨y, hy⟩ := hgen.specializes (hle (subset_closure rfl))
    exact congrArg Subtype.val (hyq'.antisymm hqy).eq

open Classical in
/-- **The components of a connected fibre form a connected curve.** Let `f : U ⟶ Z` have a
closed connected fibre `F = f⁻¹(w)`, and let `S` be curves of the open `U ⊆ X` whose generic
points are the maximal points of `F`. If each `C ∈ S` is the proper curve `Γ C` of `X`, then
`⋃_{C ∈ S} Γ C` contains `F` and is connected. -/
private theorem isConnected_curveUnion_of_fiber {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) {Z : Scheme.{u}} (f : U.toScheme ⟶ Z) {w : Z}
    (hFc : _root_.IsConnected (f ⁻¹' {w})) (hFcl : IsClosed (f ⁻¹' {w}))
    (S : Finset (ProperCurve (U.ι ≫ sX)))
    (hS : Mori.ProperCurve.point '' (S : Set (ProperCurve (U.ι ≫ sX))) =
      {x | f x = w ∧ ∀ y, f y = w → y ⤳ x → y = x})
    (Γ : ProperCurve (U.ι ≫ sX) → ProperCurve sX) (hΓ : ∀ C, (Γ C).point = U.ι C.point) :
    U.ι '' (f ⁻¹' {w}) ⊆ curveUnion sX (S.image Γ) ∧
      _root_.IsConnected (curveUnion sX (S.image Γ)) := by
  have hA : U.ι '' (f ⁻¹' {w}) ⊆ curveUnion sX (S.image Γ) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hqF, hqp, hqmax⟩ := exists_maximal_generization hFcl hp
    obtain ⟨C, hCS, rfl⟩ : q ∈ Mori.ProperCurve.point '' (S : Set (ProperCurve (U.ι ≫ sX))) := by
      rw [hS]
      exact ⟨hqF, hqmax⟩
    refine Set.mem_biUnion (Finset.mem_image_of_mem Γ hCS) ?_
    rw [hΓ]
    exact specializes_iff_mem_closure.mp (hqp.map U.ι.continuous)
  have hcl : curveUnion sX (S.image Γ) ⊆ closure (U.ι '' (f ⁻¹' {w})) := by
    refine Set.iUnion₂_subset fun Γ' hΓ' => ?_
    obtain ⟨C, hCS, rfl⟩ := Finset.mem_image.mp hΓ'
    have hC : C.point ∈ Mori.ProperCurve.point '' (S : Set (ProperCurve (U.ι ≫ sX))) :=
      ⟨C, hCS, rfl⟩
    rw [hS] at hC
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨C.point, hC.1, (hΓ C).symm⟩)
  exact ⟨hA, (hFc.image _ U.ι.continuous.continuousOn).subset_closure hA hcl⟩

end FA15Helpers

/-- A proper curve whose generic point lies on a finite union of proper curves is one of them:
its generic point specializes from the generic point of one of them, and a proper
specialization of the generic point of a curve is a closed point. -/
private theorem mem_of_point_mem_curveUnion {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [JacobsonSpace X] {S : Finset (ProperCurve sX)} (C : ProperCurve sX)
    (h : C.point ∈ curveUnion sX S) : C ∈ S := by
  obtain ⟨C', hC', hmem⟩ := Set.mem_iUnion₂.mp h
  have hsp : C'.point ⤳ C.point := specializes_iff_mem_closure.mpr hmem
  by_cases he : C'.point = C.point
  · rwa [show C = C' from (Mori.ProperCurve.ext he).symm]
  · exfalso
    have hcl := MMP.Chow.FixedDegreeCurveCyclesProof.ProperCurve.isClosed_singleton_of_specializes
      C' hsp he
    obtain ⟨w, hw, hwne⟩ :=
      MMP.Chow.DeterminantCurveForm.exists_specializes_ne_of_isProperCurve sX C.point
        C.isProperCurve
    have := specializes_iff_mem_closure.mp hw
    rw [hcl.closure_eq, Set.mem_singleton_iff] at this
    exact hwne this

/-- Every point of a set `I` lies on a maximal irreducible subset of `I`. -/
private theorem exists_maximal_isIrreducible_subset {T : Type*} [TopologicalSpace T]
    {I : Set T} {p : T} (hp : p ∈ I) :
    ∃ Y, Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Y ∧ p ∈ Y := by
  obtain ⟨m, hpm, hm⟩ := zorn_subset_nonempty {t : Set T | IsPreirreducible t ∧ t ⊆ I}
    (fun c hc hcc _ =>
      ⟨⋃₀ c, ⟨fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
        let ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
        let ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
        Or.casesOn (hcc.total hpc hqc)
          (fun hpq : p ⊆ q =>
            let ⟨x, hxp, hxuv⟩ := (hc hqc).1 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
            ⟨x, Set.mem_sUnion_of_mem hxp hqc, hxuv⟩)
          fun hqp : q ⊆ p =>
          let ⟨x, hxp, hxuv⟩ := (hc hpc).1 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
          ⟨x, Set.mem_sUnion_of_mem hxp hpc, hxuv⟩,
        Set.sUnion_subset fun t ht => (hc ht).2⟩,
        fun _ hxc => Set.subset_sUnion_of_mem hxc⟩)
    {p} ⟨isPreirreducible_singleton, Set.singleton_subset_iff.mpr hp⟩
  refine ⟨m, ⟨⟨⟨⟨p, hpm rfl⟩, hm.1.1⟩, hm.1.2⟩, fun Z hZ hmZ => ?_⟩, hpm rfl⟩
  exact hm.2 ⟨hZ.1.2, hZ.2⟩ hmZ

/-- A closed set each of whose maximal irreducible subsets has dense image under `f` is the
closure of its part over a nonempty open set. -/
private theorem eq_closure_inter_preimage_of_forall_maximal_dense {T B : Type*}
    [TopologicalSpace T] [TopologicalSpace B] {f : T → B} (hf : Continuous f) {I : Set T}
    {O : Set B} (hI : IsClosed I) (hO : IsOpen O) (hOne : O.Nonempty)
    (hdom : ∀ Y, Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Y → Dense (f '' Y)) :
    I = closure (I ∩ f ⁻¹' O) := by
  refine Set.Subset.antisymm (fun p hp => ?_) (hI.closure_subset_iff.mpr Set.inter_subset_left)
  obtain ⟨Y, hY, hpY⟩ := exists_maximal_isIrreducible_subset hp
  obtain ⟨_, hbO, y, hy, rfl⟩ := (hdom Y hY).inter_open_nonempty O hO hOne
  exact closure_mono (Set.inter_subset_inter_left _ hY.1.2)
    (subset_closure_inter_of_isPreirreducible_of_isOpen hY.1.1.isPreirreducible
      (hO.preimage hf) ⟨y, hy, hbO⟩ hpY)

/-- `3 ≤ a + 2` forces `1 ≤ a` in `WithBot ℕ∞`. -/
private theorem one_le_of_three_le_add_two {a : WithBot ℕ∞} (h : (3 : WithBot ℕ∞) ≤ a + 2) :
    1 ≤ a := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe b =>
    have h2 : (3 : ℕ∞) ≤ b + 2 := WithBot.coe_le_coe.mp (by rwa [WithBot.coe_add])
    induction b using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe n =>
      have h3 : 3 ≤ n + 2 := by exact_mod_cast h2
      exact_mod_cast (show 1 ≤ n by omega)

/-- `1 < a` forces `2 ≤ a` in `WithBot ℕ∞`. -/
private theorem two_le_of_one_lt {a : WithBot ℕ∞} (h : 1 < a) : 2 ≤ a := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe b =>
    have h2 : (1 : ℕ∞) < b := WithBot.coe_lt_coe.mp h
    induction b using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe n =>
      have h3 : 1 < n := by exact_mod_cast h2
      exact WithBot.coe_le_coe.mpr (by exact_mod_cast (show 2 ≤ n by omega))

/-- The irreducible components of a topological fibre `g⁻¹(z)` are those of the scheme fibre
`g.fiber z`, with the same dimensions. -/
private theorem topologicalKrullDim_of_mem_irreducibleComponents_preimage {X Y : Scheme.{u}}
    (g : X ⟶ Y) (z : Y) {n : WithBot ℕ∞}
    (h : ∀ W ∈ irreducibleComponents (g.fiber z), topologicalKrullDim W = n)
    (Y' : Set (g.base ⁻¹' {z})) (hY : Y' ∈ irreducibleComponents (g.base ⁻¹' {z})) :
    topologicalKrullDim Y' = n := by
  have hYf := image_mem_irreducibleComponents_of_homeomorph (g.fiberHomeo z).symm hY
  rw [← h _ hYf]
  refine MMP.Chow.FixedDegreeCurveCyclesProof.topologicalKrullDim_eq_of_range_eq
    Topology.IsEmbedding.subtypeVal
    ((g.fiberHomeo z).isEmbedding.comp Topology.IsEmbedding.subtypeVal) ?_
  rw [Subtype.range_coe, Set.range_comp, Subtype.range_coe]
  exact ((g.fiberHomeo z).image_symm_image Y').symm

/-- **The good open of a log elliptic fibre space.** There is a nonempty open `Z₁ ⊆ Z`, smooth
over `k`, over which `f_U` is smooth, whose fibres have one-dimensional components, and over whose
closed points every curve of the fibre is `(K_X + Δ_X)`-trivial: the degree of `K_X + Δ_X` on the
generic fibre is zero, it is the sum of the nonnegative intersection numbers with the components
of a closed fibre, and these components form a connected curve containing the fibre. -/
private theorem exists_open_smooth_trivial_fibres
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType (i ≫ projToSpecCoeff k N)] [QuasiCompact (i ≫ projToSpecCoeff k N)]
    {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k (i ≫ projToSpecCoeff k N) K Δ)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ i ≫ projToSpecCoeff k N) sZ 3
      (DivisorWithCoeffs.restrict U.ι K) (DivisorWithCoeffs.restrict U.ι Δ) fU) :
    ∃ Z₁ : Z.Opens, (Z₁ : Set Z).Nonempty ∧
      Smooth (fU ∣_ Z₁) ∧ Smooth (Z₁.ι ≫ sZ) ∧
      (∀ w ∈ Z₁, ∀ Y ∈ irreducibleComponents (fU.fiber w), topologicalKrullDim Y = 1) ∧
      (∀ w ∈ Z₁, IsClosed ({w} : Set Z) → ∀ C : ProperCurve (i ≫ projToSpecCoeff k N),
        closure {C.point} ⊆ U.ι '' (fU ⁻¹' {w}) →
        (Divisor.toQDivisor K + Δ).intersectionNumber k (i ≫ projToSpecCoeff k N) C.ι C.dim_le
          h.isQCartier = 0) := by
  classical
  set sX := i ≫ projToSpecCoeff k N with hsX
  have hc := hfU.isContraction
  have hZv : Mori.IsVariety k sZ := hc.isVariety_target
  have hUv : Mori.IsVariety k (U.ι ≫ sX) := hc.isVariety_source
  haveI := hZv.toIsIntegral
  haveI := hZv.toLocallyOfFiniteType
  haveI := hZv.toIsSeparated
  haveI := hZv.toQuasiCompact
  haveI : IsProper fU := hc.isProper
  set L := Divisor.toQDivisor K + Δ with hLdef
  haveI : IsIntegral U.toScheme := hUv.toIsIntegral
  haveI : IsSeparated (U.ι ≫ sX) := hUv.toIsSeparated
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := hUv.toLocallyOfFiniteType
  haveI : QuasiCompact (U.ι ≫ sX) := hUv.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI hsurj : Surjective fU := fU.surjective_of_isIso_app hc.isIso_app
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hU)
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hdim : topologicalKrullDim U.toScheme = topologicalKrullDim Z + 1 :=
    topologicalKrullDim_eq_add_one (U.ι ≫ sX) sZ fU hc.comp_eq hsurj.surj hfU.dim_genericFiber
  obtain ⟨V₁, hV₁d, hV₁sm, hV₁⟩ :=
    exists_dense_open_smooth_restrict (U.ι ≫ sX) sZ fU hc.comp_eq hdim
  set LU := Divisor.toQDivisor (DivisorWithCoeffs.restrict U.ι K) +
    DivisorWithCoeffs.restrict U.ι Δ with hLUdef
  have hLU_eq : LU = L.restrictOpen U := by
    rw [hLUdef, restrict_ι_eq_restrictOpen, restrict_ι_eq_restrictOpen]
    ext P
    rfl
  have hLUq : QDivisor.IsQCartier (L.restrictOpen U) := hLU_eq ▸ hfU.isQCartier
  obtain ⟨V₂, hV₂d, hV₂⟩ := exists_dense_open_genericFiberDegree_eq_sum_intersectionNumber
    (U.ι ≫ sX) sZ fU hc.comp_eq hdim LU hfU.isQCartier
  obtain ⟨V₃, hV₃sm, hη₃⟩ : ∃ V₃ : Z.Opens, Smooth (V₃.ι ≫ sZ) ∧ genericPoint Z ∈ V₃ := by
    have h := MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus' (k := k) (f := sZ)
    obtain ⟨V, hV, hηV⟩ := TopologicalSpace.Opens.mem_sSup.mp h
    exact ⟨V, hV, hηV⟩
  have hgen : ∀ V : Z.Opens, Dense (V : Set Z) → genericPoint Z ∈ V := fun V hV =>
    ((genericPoint_spec Z).mem_open_set_iff V.isOpen).mpr (by simpa using hV.nonempty)
  set W : V₁.toScheme.Opens := V₁.ι ⁻¹ᵁ (V₂ ⊓ V₃) with hW
  set Z₁ : Z.Opens := V₁.ι ''ᵁ W with hZ₁def
  have hmem : ∀ w, w ∈ Z₁ ↔ w ∈ V₁ ∧ w ∈ V₂ ∧ w ∈ V₃ := by
    intro w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, hv.1, hv.2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨w, h1⟩, ⟨h2, h3⟩, rfl⟩
  have hle₃ : Z₁ ≤ V₃ := fun w hw => ((hmem w).1 hw).2.2
  refine ⟨Z₁, ⟨genericPoint Z, (hmem _).2 ⟨hgen V₁ hV₁d, hgen V₂ hV₂d, hη₃⟩⟩, ?_, ?_,
    fun w hw => (hV₁ w ((hmem w).1 hw).1).2, ?_⟩
  · exact smooth_morphismRestrict_image fU V₁ W
  · rw [← Z.homOfLE_ι hle₃, Category.assoc]
    infer_instance
  · intro w hw hwc C hC
    obtain ⟨-, hw2, -⟩ := (hmem w).1 hw
    obtain ⟨S, hSpts, hdeg⟩ := (hV₂ w hw2).2 hwc
    choose Γ e hΓpt hΓe using fun C : ProperCurve (U.ι ≫ sX) =>
      exists_properCurve_of_opens sX U C
    have hcmp : ∀ C : ProperCurve (U.ι ≫ sX),
        LU.intersectionNumber k (U.ι ≫ sX) C.ι C.dim_le hfU.isQCartier =
          L.intersectionNumber k sX (Γ C).ι (Γ C).dim_le h.isQCartier := fun C => by
      rw [Fourfold.intersectionNumber_congr (U.ι ≫ sX) C.ι C.dim_le _ hLUq hLU_eq]
      exact intersectionNumber_restrictOpen_of_iso sX U L h.isQCartier hLUq C (Γ C) (e C) (hΓe C)
    have hzero : ∀ C ∈ S, L.intersectionNumber k sX (Γ C).ι (Γ C).dim_le h.isQCartier = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun C _ =>
        h.isNef.2 (Γ C).scheme (Γ C).ι (Γ C).dim_eq).mp ?_
      rw [← Finset.sum_congr rfl fun C _ => hcmp C, ← hdeg]
      exact hfU.genericFiberDegree_eq_zero
    obtain ⟨hA, -⟩ := isConnected_curveUnion_of_fiber sX U fU
      (fU.isConnected_preimage_singleton_of_isIso_app hc.isIso_app w)
      (hwc.preimage fU.continuous) S hSpts Γ hΓpt
    obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp
      (mem_of_point_mem_curveUnion C (hA (hC (subset_closure rfl))))
    exact hzero C₀ hC₀

/-- Two closed sets of a Jacobson space with the same closed points are equal. -/
private theorem eq_of_isClosed_of_forall_isClosed_singleton {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {A B : Set T} (hA : IsClosed A) (hB : IsClosed B)
    (h : ∀ x, IsClosed ({x} : Set T) → (x ∈ A ↔ x ∈ B)) : A = B := by
  rw [← JacobsonSpace.closure_inter_closedPoints hA, ← JacobsonSpace.closure_inter_closedPoints hB]
  congr 1
  ext x
  exact ⟨fun ⟨h1, h2⟩ => ⟨(h x h2).1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h x h2).2 h1, h2⟩⟩

/-- If `f` is an isomorphism on sections over every open, so is its restriction over `O`. -/
private theorem isIso_c_morphismRestrict {V T : Scheme.{u}} (f : V ⟶ T)
    (hf : ∀ O : T.Opens, IsIso (f.app O)) (O : T.Opens) : IsIso (f ∣_ O).c := by
  haveI : ∀ W, IsIso ((f ∣_ O).c.app W) := fun W => by
    change IsIso ((f ∣_ O).app W.unop)
    rw [morphismRestrict_app]
    have h1 := hf (O.ι ''ᵁ W.unop)
    have h2 : IsIso (V.presheaf.map
        (eqToHom (image_morphismRestrict_preimage f O W.unop)).op) :=
      Functor.map_isIso _ _
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  exact NatIso.isIso_of_isIso_app _

/-- Over closed points `z` of `Y` and `x` of `X`, the fibre product `Y ×ₖ X` has exactly one
point, and it is closed. -/
private theorem exists_unique_closed_point_pullback {k : Type u} [Field k] [IsAlgClosed k]
    {Y X : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (z : Y) (x : X) (hz : IsClosed ({z} : Set Y)) (hx : IsClosed ({x} : Set X)) :
    ∃ p : (pullback sY sX : Scheme.{u}), pullback.fst sY sX p = z ∧
      pullback.snd sY sX p = x ∧ IsClosed ({p} : Set (pullback sY sX : Scheme.{u})) ∧
      ∀ p' : (pullback sY sX : Scheme.{u}), pullback.fst sY sX p' = z →
        pullback.snd sY sX p' = x → p' = p := by
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := sY) (g := sX) z x
    (Subsingleton.elim _ _)
  have huniq : ∀ p' : (pullback sY sX : Scheme.{u}), pullback.fst sY sX p' = z →
      pullback.snd sY sX p' = x → p' = p := fun p' h1 h2 =>
    Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap sY sX p' p
      (h1.trans hp1.symm) (h2.trans hp2.symm)
      (MMP.Chow.FixedDegreeCurveCyclesProof.isIso_residueFieldMap_of_isClosed sX _ (hp2 ▸ hx))
  refine ⟨p, hp1, hp2, ?_, huniq⟩
  have hset : ({p} : Set (pullback sY sX : Scheme.{u})) =
      pullback.fst sY sX ⁻¹' {z} ∩ pullback.snd sY sX ⁻¹' {x} :=
    Set.ext fun p' => ⟨by rintro rfl; exact ⟨hp1, hp2⟩, fun ⟨h1, h2⟩ => huniq p' h1 h2⟩
  rw [hset]
  exact (hz.preimage (pullback.fst sY sX).continuous).inter
    (hx.preimage (pullback.snd sY sX).continuous)

/-- A closed `I ⊆ Y ×ₖ X` whose closed points over `z` are those over the closed set `F z`
projects, over a closed point `z`, onto `F z`. -/
private theorem snd_image_inter_fst_preimage_eq {k : Type u} [Field k] [IsAlgClosed k]
    {Y X : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [JacobsonSpace X] [IsProper (pullback.snd sY sX)]
    {I : Set (pullback sY sX : Scheme.{u})} (hIc : IsClosed I) (F : Y → Set X)
    (hF : ∀ z, IsClosed (F z))
    (hIpts : ∀ p : (pullback sY sX : Scheme.{u}), IsClosed {p} →
      (p ∈ I ↔ pullback.snd sY sX p ∈ F (pullback.fst sY sX p)))
    (z : Y) (hz : IsClosed ({z} : Set Y)) :
    pullback.snd sY sX '' (I ∩ pullback.fst sY sX ⁻¹' {z}) = F z := by
  have hA : IsClosed (pullback.snd sY sX '' (I ∩ pullback.fst sY sX ⁻¹' {z})) :=
    (pullback.snd sY sX).isClosedMap _ (hIc.inter (hz.preimage (pullback.fst sY sX).continuous))
  refine eq_of_isClosed_of_forall_isClosed_singleton hA (hF z) fun x hxc => ⟨fun hx => ?_,
    fun hx => ?_⟩
  · obtain ⟨p', ⟨hp'I, hp'1⟩, hp'2⟩ := hx
    obtain ⟨p, hp1, hp2, hpc, huniq⟩ := exists_unique_closed_point_pullback sY sX z x hz hxc
    rw [huniq p' hp'1 hp'2] at hp'I
    have := (hIpts p hpc).1 hp'I
    rwa [hp1, hp2] at this
  · obtain ⟨p, hp1, hp2, hpc, -⟩ := exists_unique_closed_point_pullback sY sX z x hz hxc
    exact ⟨p, ⟨(hIpts p hpc).2 (by rwa [hp1, hp2]), hp1⟩, hp2⟩

/-- The `𝒪(1)`-degree of a 1-cycle on `X ⊆ ℙᴺ_k` is the weighted sum of the degrees of its
curves. -/
private theorem projDegree_eq_sum {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {N : ℕ} (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)) :
    projDegree i Z = Z.sum fun C a => a * MMP.Chow.DeterminantCurveForm.curveDeg
      (MMP.Chow.FixedDegreeCurveCyclesProof.ProperCurve.mapClosedImmersion i
        (projToSpecCoeff k N) C) := by
  simp only [projDegree]
  rw [MMP.Chow.FixedDegreeCurveCyclesProof.pushforward_eq_mapDomain]
  erw [Mori.OneCycle.degree_apply]
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  rfl

/-- The effective 1-cycles of degree `d` on `X ⊆ ℙᴺ_k` supported on a finite set `S` of curves
form a finite set. -/
private theorem finite_setOf_projDegree_eq {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {N : ℕ} (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (S : Finset (ProperCurve (i ≫ projToSpecCoeff k N))) :
    {Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N) |
      0 ≤ Z ∧ projDegree i Z = d ∧ ∀ C ∈ Z.support, C ∈ S}.Finite := by
  set T : Set (Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)) :=
    {Z | 0 ≤ Z ∧ projDegree i Z = d ∧ ∀ C ∈ Z.support, C ∈ S}
  have hbound : ∀ Z ∈ T, ∀ C, Z C ≤ d := by
    rintro Z ⟨hZ0, hZd, -⟩ C
    by_cases hC : C ∈ Z.support
    · rw [← hZd, projDegree_eq_sum, Finsupp.sum]
      have hpos := MMP.Chow.DeterminantCurveForm.curveDeg_pos
        (MMP.Chow.FixedDegreeCurveCyclesProof.ProperCurve.mapClosedImmersion i
          (projToSpecCoeff k N) C)
      calc Z C ≤ Z C * MMP.Chow.DeterminantCurveForm.curveDeg
            (MMP.Chow.FixedDegreeCurveCyclesProof.ProperCurve.mapClosedImmersion i
              (projToSpecCoeff k N) C) := le_mul_of_one_le_right (hZ0 C) (by omega)
        _ ≤ _ := Finset.single_le_sum (f := fun C => Z C * MMP.Chow.DeterminantCurveForm.curveDeg
            (MMP.Chow.FixedDegreeCurveCyclesProof.ProperCurve.mapClosedImmersion i
              (projToSpecCoeff k N) C))
            (fun C' _ => mul_nonneg (hZ0 C')
              (MMP.Chow.DeterminantCurveForm.curveDeg_pos _).le) hC
    · rw [Finsupp.notMem_support_iff.mp hC]
      exact_mod_cast Nat.zero_le d
  refine Set.Finite.of_finite_image (f := fun Z : Mori.OneCycle ℤ _ => fun C : S => Z C) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : S => Set.Icc (0 : ℤ) d)
      fun _ => Set.finite_Icc _ _).subset ?_
    rintro _ ⟨Z, hZ, rfl⟩ C _
    exact ⟨hZ.1 C, hbound Z hZ C⟩
  · intro Z hZ Z' hZ' he
    ext C
    by_cases hC : C ∈ S
    · exact congrFun he ⟨C, hC⟩
    · rw [Finsupp.notMem_support_iff.mp (fun h => hC (hZ.2.2 C h)),
        Finsupp.notMem_support_iff.mp (fun h => hC (hZ'.2.2 C h))]

/-- A fibre of `g` over a closed point which `u` maps onto the support of a 1-cycle, with
`(g, u)` a closed immersion, has components of dimension at most one. -/
private theorem topologicalKrullDim_le_one_of_image_fiber_eq_cycleSupport {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [LocallyOfFiniteType sZ]
    (g : Y ⟶ Z) (u : Y ⟶ X) (hgu : g ≫ sZ = u ≫ sX) [IsClosedImmersion (pullback.lift g u hgu)]
    {z : Z} (hz : IsClosed ({z} : Set Z)) (Zc : Mori.OneCycle ℤ sX)
    (hsupp : u.base '' (g.base ⁻¹' {z}) = cycleSupport Zc) :
    ∀ W ∈ irreducibleComponents (g.fiber z), topologicalKrullDim W ≤ 1 := by
  intro W hW
  haveI := MMP.Chow.FixedDegreeCurveCyclesProof.isClosedImmersion_fiberι_comp sZ sX g u hgu hz
  set m := g.fiberι z ≫ u
  have hmW : IsIrreducible (m '' W) := hW.1.image m m.continuous.continuousOn
  have hrange : m '' W ⊆ cycleSupport Zc := by
    rw [← hsupp]
    rintro _ ⟨w, -, rfl⟩
    refine ⟨g.fiberι z w, ?_, rfl⟩
    have := ((g.fiberHomeo z) w).2
    rwa [Scheme.Hom.fiberHomeo_apply] at this
  obtain ⟨_, hmem, hCsub⟩ := (isIrreducible_iff_sUnion_isClosed.mp hmW)
    (Zc.support.image fun C => closure ({C.point} : Set X))
    (fun t ht => by
      obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp ht
      exact isClosed_closure)
    (by
      refine hrange.trans fun x hx => ?_
      obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_sUnion.mpr ⟨_, by
        rw [Finset.coe_image]; exact ⟨C, Finset.mem_coe.mpr hC, rfl⟩,
        hxC⟩)
  obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hmem
  have h1 : topologicalKrullDim W = topologicalKrullDim (m '' W) :=
    MMP.Chow.FixedDegreeCurveCyclesProof.topologicalKrullDim_eq_of_range_eq
      (m.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal)
      Topology.IsEmbedding.subtypeVal (by rw [Set.range_comp, Subtype.range_coe,
        Subtype.range_coe])
  rw [h1]
  calc topologicalKrullDim (m '' W) ≤ topologicalKrullDim (closure ({C.point} : Set X)) :=
        (Topology.IsEmbedding.inclusion hCsub).isInducing.topologicalKrullDim_le
    _ = 1 := by rw [← topologicalKrullDim_curveSubschemeAt]; exact C.dim_eq

/-- A dominant morphism `g` from a threefold onto a surface whose closed fibres have components
of dimension at most one has all fibre components of dimension one: the locus where the fibre
dimension is at least two is closed and, were it nonempty, would contain a closed point. -/
private theorem topologicalKrullDim_fiber_eq_one {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] (g : Y ⟶ Z) (hg : g ≫ sZ = sY) [IsDominant g]
    [LocallyOfFiniteType g] [JacobsonSpace Y] [JacobsonSpace Z]
    (hY : topologicalKrullDim Y = 3) (hZ : topologicalKrullDim Z = 2)
    (hclosed : ∀ z : Z, IsClosed ({z} : Set Z) →
      ∀ W ∈ irreducibleComponents (g.fiber z), topologicalKrullDim W ≤ 1)
    (z : Z) : ∀ W ∈ irreducibleComponents (g.fiber z), topologicalKrullDim W = 1 := by
  obtain ⟨hlower, -, hsemi⟩ := MMP.topologicalKrullDim_fiber_of_isDominant k sY sZ g hg
  intro W hW
  refine le_antisymm ?_ (one_le_of_three_le_add_two (by
    rw [← hY, ← hZ]; exact hlower z W hW))
  by_contra hlt
  have h2 : (2 : WithBot ℕ∞) ≤ topologicalKrullDim W := two_le_of_one_lt (not_le.mp hlt)
  haveI : LocallyOfFiniteType (g.fiberToSpecResidueField z) :=
    locallyOfFiniteType_fiberToSpecResidueField k sY sZ g hg z
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)
  have hdimξ : (2 : WithBot ℕ∞) ≤ topologicalKrullDimAt (g.fiber z) ξ := by
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents (Z.residueField z) (g.fiber z)
      (g.fiberToSpecResidueField z) ξ]
    exact h2.trans (le_iSup₂ (f := fun W (_ : W ∈ {W ∈ irreducibleComponents (g.fiber z) |
      ξ ∈ W}) => topologicalKrullDim W) W ⟨hW, hξ.mem⟩)
  have htrans : ∀ (z' : Z), z' = z → ∀ w : g.fiber z', g.fiberι z' w = g.fiberι z ξ →
      topologicalKrullDimAt (g.fiber z') w = topologicalKrullDimAt (g.fiber z) ξ := by
    rintro _ rfl w hw
    have hwξ : w = ξ := (g.fiberHomeo _).injective (Subtype.ext (by
      rwa [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberHomeo_apply]))
    rw [hwξ]
  obtain ⟨y, hy⟩ : ∃ y, y = g.fiberι z ξ := ⟨_, rfl⟩
  have hgy : g y = z := by
    rw [hy]
    have := ((g.fiberHomeo z) ξ).2
    rwa [Scheme.Hom.fiberHomeo_apply] at this
  have hyC : y ∈ {x : Y | ((2 : ℕ) : WithBot ℕ∞) ≤
      topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x)} := by
    change ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDimAt (g.fiber (g y)) (g.asFiber y)
    rw [htrans _ hgy _ ((g.fiberι_asFiber y).trans hy)]
    exact_mod_cast hdimξ
  obtain ⟨y', hy'C, hy'c⟩ := nonempty_inter_closedPoints ⟨y, hyC⟩ (hsemi 2).isLocallyClosed
  have hz' : IsClosed ({g y'} : Set Z) := g.closePoints_subset_preimage_closedPoints hy'c
  haveI : LocallyOfFiniteType (g.fiberToSpecResidueField (g y')) :=
    locallyOfFiniteType_fiberToSpecResidueField k sY sZ g hg (g y')
  have hle : topologicalKrullDimAt (g.fiber (g y')) (g.asFiber y') ≤ 1 := by
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents (Z.residueField (g y'))
      (g.fiber (g y')) (g.fiberToSpecResidueField (g y')) _]
    exact iSup₂_le fun W' hW' => hclosed (g y') hz' W' hW'.1
  exact absurd (show ((2 : ℕ) : WithBot ℕ∞) ≤ 1 from hy'C.trans hle) (by decide)

/-- On a family of effective 1-cycles whose degrees of invertible sheaves are constant on
connected components, if every curve of one cycle is `(K_X + Δ_X)`-trivial then so is every
curve of each cycle in its connected component, by nefness of `K_X + Δ_X`. -/
private theorem intersectionNumber_eq_zero_of_mem_connectedComponent
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k sX K Δ) {𝒞 : Scheme.{u}}
    (cycOf : 𝒞 → Mori.OneCycle ℤ sX) (heff : ∀ c : 𝒞, IsClosed ({c} : Set 𝒞) → 0 ≤ cycOf c)
    (hconst : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      ∀ c c' : 𝒞, IsClosed ({c} : Set 𝒞) → IsClosed ({c'} : Set 𝒞) →
        c' ∈ connectedComponent c →
          Mori.OneCycle.degree ℤ sX L (cycOf c) = Mori.OneCycle.degree ℤ sX L (cycOf c'))
    {c c₀ : 𝒞} (hc : IsClosed ({c} : Set 𝒞)) (hc₀ : IsClosed ({c₀} : Set 𝒞))
    (hconn : c₀ ∈ connectedComponent c)
    (htriv : ∀ C' ∈ (cycOf c₀).support,
      (Divisor.toQDivisor K + Δ).intersectionNumber k sX C'.ι C'.dim_le h.isQCartier = 0)
    {C : ProperCurve sX} (hC : C ∈ (cycOf c).support) :
    (Divisor.toQDivisor K + Δ).intersectionNumber k sX C.ι C.dim_le h.isQCartier = 0 := by
  obtain ⟨Nd, hN, hNc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul h.isQCartier
  have hm := QDivisor.cartierIndex_pos h.isQCartier
  haveI := hNc.isInvertibleModule_divisorialSheaf
  have hdegC : ∀ C' : ProperCurve sX,
      (Divisor.toQDivisor K + Δ).intersectionNumber k sX C'.ι C'.dim_le h.isQCartier =
        (C'.degree k Nd.divisorialSheaf : ℚ) /
          (Divisor.toQDivisor K + Δ).cartierIndex h.isQCartier := fun C' => by
    rw [ProperCurve.degree_divisorialSheaf]
    exact QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C'.ι C'.dim_le _ _ Nd hNc hN
  have hnef : ∀ C' : ProperCurve sX, 0 ≤ C'.degree k Nd.divisorialSheaf := fun C' => by
    have h0 := h.isNef.2 C'.scheme C'.ι C'.dim_eq
    rw [hdegC] at h0
    have hm' : (0 : ℚ) < (Divisor.toQDivisor K + Δ).cartierIndex h.isQCartier := by
      exact_mod_cast hm
    exact_mod_cast (div_nonneg_iff.mp h0).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hm')
  have hdeg0 : Mori.OneCycle.degree ℤ sX Nd.divisorialSheaf (cycOf c₀) = 0 := by
    rw [Mori.OneCycle.degree_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun C' hC' => ?_
    have h0 := htriv C' hC'
    rw [hdegC, div_eq_zero_iff] at h0
    have : C'.degree k Nd.divisorialSheaf = 0 := by
      rcases h0 with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 (by exact_mod_cast hm.ne')
    rw [this, Int.cast_zero, mul_zero]
  have hdegc := (hconst Nd.divisorialSheaf c c₀ hc hc₀ hconn).trans hdeg0
  rw [Mori.OneCycle.degree_apply, Finsupp.sum] at hdegc
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun C' _ => mul_nonneg
    (heff c hc C') (hnef C'))).mp hdegc C hC
  have hC0 : C.degree k Nd.divisorialSheaf = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (Finsupp.mem_support_iff.mp hC)
  rw [hdegC, hC0, Int.cast_zero, zero_div]

/-- Over a finite `φ : B ⟶ 𝒞_d(X)`, only finitely many closed points of `B` have a fibre, with
the support of its cycle, inside a given finite union of curves. -/
private theorem finite_setOf_isClosed_subset_curveUnion {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [JacobsonSpace X] {N : ℕ}
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i] {𝒞 B : Scheme.{u}}
    [JacobsonSpace 𝒞]
    {cycOf : 𝒞 → Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)} {d : ℕ}
    (hbij : Set.BijOn cycOf {c | IsClosed ({c} : Set 𝒞)} {Z | 0 ≤ Z ∧ projDegree i Z = d})
    (φ : B ⟶ 𝒞) [IsFinite φ] (F : B → Set X)
    (hF : ∀ z, IsClosed ({z} : Set B) → F z = cycleSupport (cycOf (φ z)))
    (S : Finset (ProperCurve (i ≫ projToSpecCoeff k N))) :
    {z : B | IsClosed ({z} : Set B) ∧ F z ⊆ curveUnion _ S}.Finite := by
  have hCfin : {c : 𝒞 | IsClosed ({c} : Set 𝒞) ∧
      cycOf c ∈ {Z | 0 ≤ Z ∧ projDegree i Z = d ∧ ∀ C ∈ Z.support, C ∈ S}}.Finite :=
    Set.Finite.of_finite_image
      ((finite_setOf_projDegree_eq i d S).subset (by rintro _ ⟨c, hc, rfl⟩; exact hc.2))
      (hbij.injOn.mono fun c hc => hc.1)
  refine (φ.finite_preimage hCfin).subset ?_
  rintro z ⟨hz, hsub⟩
  have hcc : IsClosed ({φ z} : Set 𝒞) := φ.closePoints_subset_preimage_closedPoints hz
  refine ⟨hcc, (hbij.mapsTo hcc).1, (hbij.mapsTo hcc).2, fun C hC => ?_⟩
  rw [hF z hz] at hsub
  exact mem_of_point_mem_curveUnion C (hsub (Set.mem_iUnion₂.mpr ⟨C, hC, subset_closure rfl⟩))

/-- For a cartesian square of `g : B ⟶ D` along an open immersion `j : C ⟶ D` of integral schemes
whose base change `π` satisfies `π_* 𝒪 = 𝒪`, the generic fibre of `g` has `Γ` equal to its base
field. -/
private theorem isIso_appTop_fiberToSpecResidueField_genericPoint {P B C D : Scheme.{u}}
    {ψ' : P ⟶ B} {π : P ⟶ C} {g : B ⟶ D} {j : C ⟶ D} [IsOpenImmersion j] [IsIntegral C]
    [IsIntegral D] [QuasiCompact π] [QuasiSeparated π] [IsIso π.c]
    (hPB : IsPullback ψ' π g j) :
    IsIso (g.fiberToSpecResidueField (genericPoint D)).appTop := by
  set η₁ := genericPoint C
  rw [← genericPoint_eq_of_isOpenImmersion j]
  haveI : IsIso (C.residue η₁) := AlgebraicGeometry.isIso_residue_genericPoint _
  haveI : Flat (C.fromSpecResidueField η₁) :=
    Stacks.AlgebraicGeometry.flat_fromSpecResidueField_of_isIso_residue η₁
  set u' := inv (Spec.map (j.residueFieldMap η₁)) ≫ C.fromSpecResidueField η₁ with hu'
  have hu'j : u' ≫ j = D.fromSpecResidueField (j η₁) := by
    rw [hu', Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      IsIso.inv_hom_id_assoc]
  haveI : Flat u' := by rw [hu']; infer_instance
  have hfib := IsPullback.of_hasPullback g (D.fromSpecResidueField (j η₁))
  have hleft : IsPullback (hPB.lift (g.fiberι (j η₁)) (g.fiberToSpecResidueField (j η₁) ≫ u')
      (by rw [Category.assoc, hu'j]; exact hfib.w)) (g.fiberToSpecResidueField (j η₁)) π u' := by
    refine IsPullback.of_right ?_ (hPB.lift_snd _ _ _) hPB
    rw [hPB.lift_fst, hu'j]
    exact hfib
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ η₁) isOpen_univ
  refine Stacks.AlgebraicGeometry.isIso_app_of_isPullback_of_flat hleft ‹_› (V := V)
    hV (isAffineOpen_top _) fun s _ => ?_
  change u' s ∈ V
  rw [hu', Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  exact hηV

/-- A morphism whose composite with a separated morphism is proper and whose composite with some
morphism is a monomorphism is a closed immersion. -/
private theorem isClosedImmersion_of_isProper_comp_of_mono_comp {T P A B : Scheme.{u}}
    (l : T ⟶ P) (p₁ : P ⟶ A) (p₂ : P ⟶ B) [IsSeparated p₁] [IsProper (l ≫ p₁)]
    [Mono (l ≫ p₂)] : IsClosedImmersion l := by
  rw [IsClosedImmersion.iff_isProper_and_mono]
  exact ⟨IsProper.of_comp l p₁, mono_of_mono l p₂⟩

/-- A morphism `φ : S ⟶ 𝒞` from a normal variety to a projective scheme over `k`, injective on
closed points, is an open immersion `S ⟶ Z̄` followed by a finite morphism `Z̄ ⟶ 𝒞`, with `Z̄`
a normal projective variety: `Z̄` is the normalization in `S` of the reduced closure of the image
of `φ`, and `S ⟶ Z̄` is an open immersion by Zariski's main theorem. -/
private theorem exists_isOpenImmersion_isFinite_of_injOn_closedPoints {k : Type u} [Field k]
    {S 𝒞 : Scheme.{u}} {sS : S ⟶ Spec (.of k)} (hSnv : Mori.IsNormalVariety k sS)
    {s𝒞 : 𝒞 ⟶ Spec (.of k)} (hproj : IsProjectiveMorphism s𝒞) (φ : S ⟶ 𝒞) (hφ : φ ≫ s𝒞 = sS)
    (hφinj : ∀ z z' : S, IsClosed ({z} : Set S) → IsClosed ({z'} : Set S) → φ z = φ z' → z = z') :
    ∃ (Zbar : Scheme.{u}) (j : S ⟶ Zbar) (φbar : Zbar ⟶ 𝒞), IsOpenImmersion j ∧ IsFinite φbar ∧
      j ≫ φbar = φ ∧ Mori.IsNormalVariety k (φbar ≫ s𝒞) ∧
        Mori.IsProjectiveVariety k (φbar ≫ s𝒞) := by
  classical
  have := hSnv.1.toIsIntegral
  have := hSnv.1.toLocallyOfFiniteType
  have := hSnv.1.toIsSeparated
  have := hSnv.1.toQuasiCompact
  have : IsNormal S := hSnv.2
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  have : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
  have : IsProper s𝒞 := isProper_of_isProjectiveMorphism s𝒞 hproj
  have : QuasiCompact (φ ≫ s𝒞) := by rw [hφ]; infer_instance
  have : LocallyOfFiniteType (φ ≫ s𝒞) := by rw [hφ]; infer_instance
  have : IsSeparated (φ ≫ s𝒞) := by rw [hφ]; infer_instance
  have : QuasiCompact φ := QuasiCompact.of_comp φ s𝒞
  have : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ s𝒞
  have : IsSeparated φ := IsSeparated.of_comp φ s𝒞
  let W : TopologicalSpace.Closeds 𝒞 := ⟨closure (Set.range φ), isClosed_closure⟩
  set J := Scheme.IdealSheafData.vanishingIdeal W with hJ
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : S ⟶ J.subscheme, ψ₀ ≫ J.subschemeι = φ :=
    ⟨IsClosedImmersion.lift _ φ (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact MMP.Chow.FixedDegreeCurveCyclesProof.vanishingIdeal_le_ker_of_isReduced φ W
        subset_closure),
      IsClosedImmersion.lift_fac _ _ _⟩
  have : LocallyOfFiniteType (ψ₀ ≫ J.subschemeι) := by rw [hψ₀]; infer_instance
  have : IsSeparated (ψ₀ ≫ J.subschemeι) := by rw [hψ₀]; infer_instance
  have : QuasiCompact (ψ₀ ≫ J.subschemeι) := by rw [hψ₀]; infer_instance
  have : LocallyOfFiniteType ψ₀ := locallyOfFiniteType_of_comp ψ₀ J.subschemeι
  have : IsSeparated ψ₀ := IsSeparated.of_comp ψ₀ J.subschemeι
  have : QuasiSeparated J.subschemeι :=
    @IsSeparated.instQuasiSeparated _ _ J.subschemeι inferInstance
  have : QuasiCompact ψ₀ := QuasiCompact.of_comp ψ₀ J.subschemeι
  have : QuasiSeparated ψ₀ := @IsSeparated.instQuasiSeparated _ _ ψ₀ ‹_›
  have : JacobsonSpace J.subscheme := LocallyOfFiniteType.jacobsonSpace (J.subschemeι ≫ s𝒞)
  have : LocallyQuasiFinite ψ₀ := locallyQuasiFinite_of_injOn_closedPoints ψ₀
    fun z z' hz hz' he => hφinj z z' hz hz' (by
      rw [← hψ₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, he])
  set Zbar := ψ₀.normalization with hZbar
  set j := ψ₀.toNormalization with hj
  set ν := ψ₀.fromNormalization with hν
  have : IsFinite ν := isFinite_fromNormalization_of_locallyOfFiniteType_over_field k
    (J.subschemeι ≫ s𝒞) sS ψ₀ (by rw [← Category.assoc, hψ₀, hφ])
  set φbar := ν ≫ J.subschemeι with hφbar
  set sZbar := φbar ≫ s𝒞 with hsZbar
  have : IsNormal Zbar := AlgebraicGeometry.isNormal_normalization ψ₀ fun V hV => by
    have : CompactSpace V := isCompact_iff_compactSpace.mp hV
    have : IsNoetherian V.toScheme := {}
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have : IsProper sZbar := by rw [hsZbar, hφbar]; infer_instance
  have hZbarnv : Mori.IsNormalVariety k sZbar := ⟨AlgebraicGeometry.IsVariety.mk, inferInstance⟩
  have hZbarproj : Mori.IsProjectiveVariety k sZbar := by
    have h1 : IsProjectiveMorphism (J.subschemeι ≫ s𝒞) :=
      (MMP.isProjectiveMorphism_of_isClosedImmersion
        J.subschemeι).comp hproj
    have hp : IsProjectiveMorphism sZbar := by
      rw [hsZbar, hφbar, Category.assoc]
      exact isProjectiveMorphism_comp_of_isFinite ν (J.subschemeι ≫ s𝒞) h1
    exact (AlgebraicGeometry.isProjectiveVariety_iff k sZbar).mpr ⟨hZbarnv.1, hp⟩
  exact ⟨Zbar, j, φbar, inferInstance, by rw [hφbar]; infer_instance,
    by rw [hφbar, hj, hν, ← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hψ₀],
    hZbarnv, hZbarproj⟩

/-- A reduced closed subscheme `W` of `P` whose points over the open `j : A ⟶ B` are the image
of a monomorphism `γ : V ⟶ P` over a proper `π : V ⟶ A` is cartesian over `j`. -/
private theorem isPullback_of_range_eq_inter_preimage_range {V W P A B : Scheme.{u}}
    (ι : W ⟶ P) [IsClosedImmersion ι] (p : P ⟶ B) (j : A ⟶ B) [IsOpenImmersion j]
    (π : V ⟶ A) [IsProper π] [IsSeparated (ι ≫ p)] [IsReduced W] (γ : V ⟶ P) [Mono γ]
    (ψ' : V ⟶ W) (hψ' : ψ' ≫ ι = γ) (hγ : γ ≫ p = π ≫ j)
    (hrange : Set.range γ.base = Set.range ι.base ∩ p.base ⁻¹' Set.range j.base) :
    IsPullback ψ' π (ι ≫ p) j := by
  have hψ'g : ψ' ≫ ι ≫ p = π ≫ j := by rw [← Category.assoc, hψ', hγ]
  set ψ := pullback.lift ψ' π hψ'g with hψ
  haveI : IsReduced (pullback (ι ≫ p) j) := isReduced_of_isOpenImmersion (pullback.fst (ι ≫ p) j)
  haveI : IsClosedImmersion ψ := by
    haveI : IsProper (ψ ≫ pullback.snd (ι ≫ p) j) := by rw [hψ, pullback.lift_snd]; infer_instance
    haveI : Mono (ψ' ≫ ι) := by rw [hψ']; infer_instance
    haveI : Mono ψ' := mono_of_mono ψ' ι
    haveI : Mono (ψ ≫ pullback.fst (ι ≫ p) j) := by rw [hψ, pullback.lift_fst]; infer_instance
    exact isClosedImmersion_of_isProper_comp_of_mono_comp ψ (pullback.snd _ j) (pullback.fst _ j)
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : ι (pullback.fst (ι ≫ p) j y) ∈ Set.range γ.base := by
      rw [hrange]
      refine ⟨⟨_, rfl⟩, pullback.snd (ι ≫ p) j y, ?_⟩
      rw [← Scheme.Hom.comp_apply (pullback.snd _ j) j, ← pullback.condition,
        Scheme.Hom.comp_apply]
      rfl
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, (pullback.fst _ j).isOpenEmbedding.injective ?_⟩
    apply ι.isClosedEmbedding.injective
    rwa [← Scheme.Hom.comp_apply ψ, hψ, pullback.lift_fst, ← Scheme.Hom.comp_apply, hψ']
  haveI : Surjective ψ := ⟨hψsurj⟩
  haveI : IsIso ψ := isIso_of_isClosedImmersion_of_surjective ψ
  exact IsPullback.of_iso_pullback ⟨hψ'g⟩ (asIso ψ) (by rw [asIso_hom, hψ, pullback.lift_fst])
    (by rw [asIso_hom, hψ, pullback.lift_snd])

/-- In a cartesian square `ψ' ≫ g = π ≫ j` with `π` surjective, a proper `g` is surjective as
soon as the range of `j` is dense. -/
private theorem surjective_of_isPullback_of_dense_range {V W A B : Scheme.{u}} {ψ' : V ⟶ W}
    {π : V ⟶ A} {g : W ⟶ B} {j : A ⟶ B} (hPB : IsPullback ψ' π g j) (hπ : Function.Surjective π)
    (hj : Dense (Set.range j)) [IsProper g] : Function.Surjective g := by
  have hrange : Set.range j ⊆ Set.range g := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := hπ z
    exact ⟨ψ' x, by rw [← Scheme.Hom.comp_apply, hPB.w, Scheme.Hom.comp_apply, hx]⟩
  intro z
  exact (g.isClosedMap.isClosed_range.closure_subset_iff.mpr hrange)
    (hj.closure_eq ▸ Set.mem_univ z)

/-- A point `c` of `Z₁ ×ₖ X` with closed second coordinate lies on the graph of `f_U ∣_ Z₁` if
and only if its second coordinate is a point of `U` over its first. -/
private theorem mem_image_iff_mem_range_lift {k : Type u} [Field k] [IsAlgClosed k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of k)}
    (U : X.Opens) (fU : U.toScheme ⟶ Z) (Z₁ : Z.Opens)
    (hπq : (fU ∣_ Z₁) ≫ Z₁.ι ≫ sZ = ((fU ⁻¹ᵁ Z₁).ι ≫ U.ι) ≫ sX)
    (c : (pullback (Z₁.ι ≫ sZ) sX : Scheme.{u}))
    (hc : IsClosed ({pullback.snd (Z₁.ι ≫ sZ) sX c} : Set X)) :
    pullback.snd (Z₁.ι ≫ sZ) sX c ∈ U.ι '' (fU ⁻¹' {Z₁.ι (pullback.fst (Z₁.ι ≫ sZ) sX c)}) ↔
      c ∈ Set.range (pullback.lift _ _ hπq) := by
  constructor
  · rintro ⟨x₀, hx₀, hxe⟩
    obtain ⟨x, rfl, hπx⟩ := exists_preimage_ι_of_apply_eq fU Z₁
      (show fU x₀ = Z₁.ι (pullback.fst _ sX c) from hx₀)
    refine ⟨x, Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap _ sX _ _ ?_ ?_
      (MMP.Chow.FixedDegreeCurveCyclesProof.isIso_residueFieldMap_of_isClosed sX _ hc)⟩
    · rwa [← Scheme.Hom.comp_apply, pullback.lift_fst]
    · rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply, hxe]
  · rintro ⟨x, rfl⟩
    have h1 : pullback.fst _ sX (pullback.lift _ _ hπq x) = (fU ∣_ Z₁) x := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    have h2 : pullback.snd _ sX (pullback.lift _ _ hπq x) = U.ι ((fU ⁻¹ᵁ Z₁).ι x) := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
    refine ⟨(fU ⁻¹ᵁ Z₁).ι x, ?_, h2.symm⟩
    change fU ((fU ⁻¹ᵁ Z₁).ι x) = Z₁.ι (pullback.fst _ sX (pullback.lift _ _ hπq x))
    rw [h1, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]

/-- The fibre components of a dominant morphism `g` from a threefold to a surface are curves as
soon as `g` embeds in `Z ×ₖ X` with each closed fibre the support of a one-cycle on `X`. -/
private theorem topologicalKrullDim_eq_one_of_image_fiber_eq_cycleSupport {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [LocallyOfFiniteType sZ] [AlgebraicGeometry.IsVariety k sZ]
    (g : Y ⟶ Z) (u : Y ⟶ X) (hgu : g ≫ sZ = u ≫ sX) [IsClosedImmersion (pullback.lift g u hgu)]
    [AlgebraicGeometry.IsVariety k (g ≫ sZ)] [IsDominant g] [LocallyOfFiniteType g]
    [JacobsonSpace Y] [JacobsonSpace Z] (hY : topologicalKrullDim Y = 3)
    (hZ : topologicalKrullDim Z = 2) (cyc : Z → Mori.OneCycle ℤ sX)
    (hsupp : ∀ z : Z, IsClosed ({z} : Set Z) → u.base '' (g.base ⁻¹' {z}) = cycleSupport (cyc z))
    (z : Z) : ∀ W ∈ irreducibleComponents (g.base ⁻¹' {z}), topologicalKrullDim W = 1 :=
  topologicalKrullDim_of_mem_irreducibleComponents_preimage g z
    (topologicalKrullDim_fiber_eq_one (g ≫ sZ) sZ g rfl hY hZ (fun z hz =>
      topologicalKrullDim_le_one_of_image_fiber_eq_cycleSupport g u hgu hz _ (hsupp z hz)) z)

/-- **Existence of a Chow closure**, for `X ⊆ ℙᴺ_k` embedded by `i`. Over a nonempty open
`Z₁ ⊆ Z`, smooth over `k`, over which `f_U` is smooth with curves as fibre components, the
fibres of `f_U` form a flat family of degree-`d` curves in `X`, classified by `φ : Z₁ ⟶ 𝒞_d(X)`.
`φ` is injective on closed points, so `Z₁` maps quasi-finitely to the reduced closure `W` of its
image, and `Z̄` is the normalization of `W` in `Z₁`: it is finite over `W`, hence normal and
projective, and `Z₁ ⟶ Z̄` is an open immersion by Zariski's main theorem. `Ū` is the support
incidence of `Z̄ ⟶ 𝒞_d(X)`. -/
private theorem exists_isChowClosure_of_isClosedImmersion
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType (i ≫ projToSpecCoeff k N)] [QuasiCompact (i ≫ projToSpecCoeff k N)]
    {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k (i ≫ projToSpecCoeff k N) K Δ)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ i ≫ projToSpecCoeff k N) sZ 3
      (DivisorWithCoeffs.restrict U.ι K) (DivisorWithCoeffs.restrict U.ι Δ) fU) :
    ∃ (Z₀ : Z.Opens) (Zbar : Scheme.{u}) (sZbar : Zbar ⟶ Spec (.of k))
        (j : Z₀.toScheme ⟶ Zbar)
        (Ubar : (pullback sZbar (i ≫ projToSpecCoeff k N)).IdealSheafData),
        IsChowClosure (sZ := sZ) (sZbar := sZbar) k (i ≫ projToSpecCoeff k N) K Δ fU Z₀ j
          Ubar := by
  classical
  set sX := i ≫ projToSpecCoeff k N with hsX
  have hc := hfU.isContraction
  have hZv : Mori.IsVariety k sZ := hc.isVariety_target
  have hUv : Mori.IsVariety k (U.ι ≫ sX) := hc.isVariety_source
  haveI := hZv.toIsIntegral
  haveI := hZv.toLocallyOfFiniteType
  haveI := hZv.toIsSeparated
  haveI := hZv.toQuasiCompact
  haveI : IsProper fU := hc.isProper
  -- Step 1: a nonempty open `Z₁ ⊆ Z`, smooth over `k`, over which `f_U` is smooth, with
  -- one-dimensional fibre components, all of whose curves are `(K_X + Δ_X)`-trivial.
  obtain ⟨Z₁, hZ₁, hsm, hsmZ, hdimfib, htriv⟩ :=
    exists_open_smooth_trivial_fibres i h U hU sZ fU hfU
  -- Step 2: the family `f_U⁻¹(Z₁) ⟶ Z₁` in `Z₁ ×ₖ X`.
  set π := fU ∣_ Z₁ with hπ
  set q := (fU ⁻¹ᵁ Z₁).ι ≫ U.ι with hq
  set sS := Z₁.ι ≫ sZ with hsS
  have hπq : π ≫ sS = q ≫ sX := by
    rw [hπ, hsS, hq, ← Category.assoc, morphismRestrict_ι, Category.assoc, hc.comp_eq,
      Category.assoc]
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : Nonempty Z₁ := ⟨⟨hZ₁.some, hZ₁.some_mem⟩⟩
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX h.isProjectiveVariety.isProjective
  have hSnv : Mori.IsNormalVariety k sS := by
    haveI : IsNormal (Spec (.of k)) :=
      isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
    haveI : IsNormal Z₁.toScheme := AlgebraicGeometry.isNormal_of_smooth sS
    exact ⟨AlgebraicGeometry.IsVariety.mk, inferInstance⟩
  have hclimm : IsClosedImmersion (pullback.lift π q hπq) := by
    haveI : IsProper (pullback.lift π q hπq ≫ pullback.fst sS sX) := by
      rw [pullback.lift_fst]
      infer_instance
    haveI : Mono (pullback.lift π q hπq ≫ pullback.snd sS sX) := by
      rw [pullback.lift_snd]
      infer_instance
    exact isClosedImmersion_of_isProper_comp_of_mono_comp _ (pullback.fst sS sX)
      (pullback.snd sS sX)
  have hfibdim : ∀ s : Z₁.toScheme, IsClosed ({s} : Set Z₁.toScheme) → ∀ x : π.fiber s,
      closure {x} ∈ irreducibleComponents (π.fiber s) →
        topologicalKrullDim (Mori.curveSubschemeAt x) = 1 := fun s _ =>
    topologicalKrullDim_curveSubschemeAt_restrict fU Z₁ s (hdimfib _ s.2)
  haveI : CompactSpace Z₁.toScheme := QuasiCompact.compactSpace_of_compactSpace sS
  obtain ⟨s₀, -, hs₀⟩ : ∃ s₀ : Z₁.toScheme, s₀ ∈ (Set.univ : Set Z₁.toScheme) ∧
      IsClosed ({s₀} : Set Z₁.toScheme) :=
    isClosed_univ.exists_closed_singleton Set.univ_nonempty
  -- the fibre cycles: effective, supported on the fibres, of constant positive degree
  have hfibcyc : ∀ s : Z₁.toScheme, IsClosed ({s} : Set Z₁.toScheme) →
      0 ≤ fibreCycle sX sS π q s ∧
        cycleSupport (fibreCycle sX sS π q s) = U.ι '' (fU ⁻¹' {Z₁.ι s}) := by
    intro s hs
    haveI := MMP.Chow.FixedDegreeCurveCyclesProof.isClosedImmersion_fiberι_comp sS sX π q hπq hs
    haveI hFp := MMP.Chow.FixedDegreeCurveCyclesProof.isProper_fiberι_comp sS π hs
    haveI : LocallyOfFiniteType (π.fiberι s ≫ π ≫ sS) := hFp.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (π.fiber s) :=
      LocallyOfFiniteType.isLocallyNoetherian (π.fiberι s ≫ π ≫ sS)
    haveI : CompactSpace (π.fiber s) :=
      QuasiCompact.compactSpace_of_compactSpace (π.fiberι s ≫ π ≫ sS)
    obtain ⟨h0, h1⟩ := cycleSupport_fibreCycle sX sS π q s
      (by simp only [Category.assoc, hπq]) (hfibdim s hs)
    exact ⟨h0, h1.trans (range_fiberι_restrict_comp fU Z₁ s U.ι)⟩
  haveI : Surjective fU := fU.surjective_of_isIso_app hc.isIso_app
  have hdimle : ∀ s : Z₁.toScheme, IsClosed ({s} : Set Z₁.toScheme) →
      topologicalKrullDim (π.fiber s) ≤ 1 := fun s _ => by
    rw [(fiberRestrictHomeo fU Z₁ s).isHomeomorph.topologicalKrullDim_eq]
    exact MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun Y hY =>
      (hdimfib _ s.2 Y hY).le
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  have hπq' : π ≫ sS = (q ≫ i) ≫ projToSpecCoeff k N := by
    rw [hπq, Category.assoc]
    rfl
  have hcd : ∀ s : Z₁.toScheme, projDegree i (fibreCycle sX sS π q s) =
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
        (MMP.Chow.FixedDegreeCurveCyclesProof.fibreCyc sS π (q ≫ i) (projToSpecCoeff k N) s) :=
    fun s => by
      simp only [projDegree, fibreCycle]
      rw [MMP.Chow.FixedDegreeCurveCyclesProof.pushforward_fiberCycle i sS π q s]
  have hdeg₀ : ∀ s : Z₁.toScheme, IsClosed ({s} : Set Z₁.toScheme) →
      projDegree i (fibreCycle sX sS π q s) = projDegree i (fibreCycle sX sS π q s₀) :=
    fun s hs => by
      rw [hcd, hcd]
      exact MMP.Chow.FixedDegreeCurveCyclesProof.degree_fibreCyc_eq sS (projToSpecCoeff k N) π
        (q ≫ i) hπq' hdimle _ hs hs₀
  have hpos : 0 < projDegree i (fibreCycle sX sS π q s₀) := by
    obtain ⟨hnn, hsp⟩ := hfibcyc s₀ hs₀
    have hne₀ : fibreCycle sX sS π q s₀ ≠ 0 := by
      intro h0
      obtain ⟨x, hx⟩ := fU.surjective (Z₁.ι s₀)
      have hmem : U.ι x ∈ cycleSupport (fibreCycle sX sS π q s₀) := by
        rw [hsp]
        exact ⟨x, hx, rfl⟩
      rw [h0] at hmem
      simp [cycleSupport] at hmem
    exact projDegree_pos i hnn hne₀
  set d := (projDegree i (fibreCycle sX sS π q s₀)).toNat with hd
  have hdZ : (d : ℤ) = projDegree i (fibreCycle sX sS π q s₀) := Int.toNat_of_nonneg hpos.le
  have hdpos : 0 < d := by omega
  have hdeg : ∀ s : Z₁.toScheme, IsClosed ({s} : Set Z₁.toScheme) →
      projDegree i (fibreCycle sX sS π q s) = d := fun s hs => (hdeg₀ s hs).trans hdZ.symm
  -- Step 3: the Chow variety and the classifying map `φ : Z₁ ⟶ 𝒞_d(X)`.
  obtain ⟨𝒞, s𝒞, cycOf, hproj, hred, hbij, hfam, hinc, hconst⟩ := exists_chowVariety_of_isIntegral i d hdpos
  obtain ⟨φ, hφ, hφc⟩ := hfam _ _ sS hSnv π q hπq hclimm inferInstance inferInstance hfibdim hdeg
  -- Step 4: the normalization `Z̄` of the closure of the image of `φ` in `Z₁`.
  haveI : IsProper s𝒞 := isProper_of_isProjectiveMorphism s𝒞 hproj
  haveI : LocallyOfFiniteType (φ ≫ s𝒞) := by rw [hφ]; infer_instance
  haveI : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ s𝒞
  have hφinj : ∀ z z' : Z₁.toScheme, IsClosed ({z} : Set Z₁.toScheme) →
      IsClosed ({z'} : Set Z₁.toScheme) → φ z = φ z' → z = z' := by
    intro z z' hz hz' he
    have hsup := congrArg cycleSupport ((hφc z hz).symm.trans (he ▸ hφc z' hz'))
    rw [(hfibcyc z hz).2, (hfibcyc z' hz').2] at hsup
    obtain ⟨x, hx⟩ := fU.surjective (Z₁.ι z)
    obtain ⟨x', hx', hxx⟩ : U.ι x ∈ U.ι '' (fU ⁻¹' {Z₁.ι z'}) := hsup ▸ ⟨x, hx, rfl⟩
    rw [U.ι.isOpenEmbedding.injective hxx] at hx'
    exact Z₁.ι.isOpenEmbedding.injective (hx.symm.trans hx')
  haveI : JacobsonSpace Z₁.toScheme := LocallyOfFiniteType.jacobsonSpace sS
  haveI : IsNormal Z₁.toScheme := hSnv.2
  obtain ⟨Zbar, j, φbar, _, _, hjφ, hZbarnv, hZbarproj⟩ :=
    exists_isOpenImmersion_isFinite_of_injOn_closedPoints hSnv hproj φ hφ hφinj
  set sZbar := φbar ≫ s𝒞 with hsZbar
  have hjc : j ≫ sZbar = Z₁.ι ≫ sZ := by rw [hsZbar, ← Category.assoc, hjφ, hφ]
  have : IsIntegral Zbar := hZbarnv.1.toIsIntegral
  have : IsNormal Zbar := hZbarnv.2
  have : IsProper sZbar := by rw [hsZbar]; infer_instance
  -- Step 5: `Ū`, the support incidence of `φ̄ : Z̄ ⟶ 𝒞_d(X)`.
  obtain ⟨I, hIc, hIpts, hIdom⟩ := hinc Zbar sZbar hZbarnv φbar rfl
  set Ubar := Scheme.IdealSheafData.vanishingIdeal ⟨I, hIc⟩ with hUbar
  -- Step 6: over `Z₁`, the incidence is the graph of `f_U`
  set e : pullback sS sX ⟶ pullback sZbar sX :=
    pullback.map sS sX sZbar sX j (𝟙 X) (𝟙 _) (by rw [Category.comp_id, hjc])
      (by rw [Category.comp_id, Category.id_comp]) with he
  have hrangeE : Set.range e = pullback.fst sZbar sX ⁻¹' Set.range j := by
    rw [he, Scheme.Pullback.range_map]
    simp
  have hgraph : MMP.Flips.chowGraph hc.comp_eq hjc = pullback.lift π q hπq ≫ e := by
    apply pullback.hom_ext
    · rw [MMP.Flips.chowGraph, pullback.lift_fst, Category.assoc, he]
      simp only [pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, π]
    · rw [MMP.Flips.chowGraph, pullback.lift_snd, Category.assoc, he]
      simp only [pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id, q]
  have hIrange : Set.range Ubar.subschemeι = I := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hφbarj : ∀ z, φbar (j z) = φ z := fun z => by rw [← Scheme.Hom.comp_apply, hjφ]
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : JacobsonSpace Zbar := LocallyOfFiniteType.jacobsonSpace sZbar
  haveI : JacobsonSpace (pullback sS sX : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst sS sX ≫ sS)
  haveI : JacobsonSpace (pullback sZbar sX : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst sZbar sX ≫ sZbar)
  have hfste : ∀ c, pullback.fst sZbar sX (e c) = j (pullback.fst sS sX c) := fun c => by
    rw [← Scheme.Hom.comp_apply, he, pullback.lift_fst, Scheme.Hom.comp_apply]
  have hsnde : ∀ c, pullback.snd sZbar sX (e c) = pullback.snd sS sX c := fun c => by
    rw [← Scheme.Hom.comp_apply, he, pullback.lift_snd, Category.comp_id]
  have hIT : e ⁻¹' I = Set.range (pullback.lift π q hπq) := by
    have key : ∀ c : (pullback sS sX : Scheme.{u}),
        IsClosed ({c} : Set (pullback sS sX : Scheme.{u})) →
        (c ∈ e ⁻¹' I ↔ c ∈ Set.range (pullback.lift π q hπq)) := by
      intro c hcc
      have hec : IsClosed ({e c} : Set (pullback sZbar sX : Scheme.{u})) :=
        e.closePoints_subset_preimage_closedPoints hcc
      have hzc : IsClosed ({pullback.fst sS sX c} : Set Z₁.toScheme) :=
        (pullback.fst sS sX).closePoints_subset_preimage_closedPoints hcc
      have hxc : IsClosed ({pullback.snd sS sX c} : Set X) :=
        (pullback.snd sS sX).closePoints_subset_preimage_closedPoints hcc
      rw [Set.mem_preimage, hIpts _ hec, hfste, hsnde, hφbarj, hφc _ hzc,
        (hfibcyc _ hzc).2]
      exact mem_image_iff_mem_range_lift U fU Z₁ hπq c hxc
    exact eq_of_isClosed_of_forall_isClosed_singleton (hIc.preimage e.continuous)
      hclimm.isClosedEmbedding.isClosed_range key
  have hL : Ubar.subschemeι.base ''
      ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' Set.range j.base) =
      I ∩ pullback.fst sZbar sX ⁻¹' Set.range j := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
      Set.image_preimage_eq_inter_range, hIrange, Set.inter_comm]
  have himpre : Ubar.subschemeι.base ''
      ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' Set.range j.base) =
      Set.range (MMP.Flips.chowGraph hc.comp_eq hjc).base := by
    rw [hgraph, hL, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hIT,
      Set.image_preimage_eq_inter_range, hrangeE]
  -- Step 7: `Ū` is integral, the closure of the graph of `f_U` over `Z₁`
  haveI : IsIntegral U.toScheme := hUv.toIsIntegral
  have hπsurj : Function.Surjective π := fun z => by
    obtain ⟨x, -, hx⟩ := exists_preimage_ι_of_apply_eq fU Z₁ (fU.surjective (Z₁.ι z)).choose_spec
    exact ⟨x, hx⟩
  haveI : Nonempty (fU ⁻¹ᵁ Z₁) := ⟨(hπsurj s₀).choose⟩
  have hGirr : IsIrreducible (Set.range (MMP.Flips.chowGraph hc.comp_eq hjc).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (MMP.Flips.chowGraph hc.comp_eq hjc).continuous.continuousOn
  have hGI : Set.range (MMP.Flips.chowGraph hc.comp_eq hjc).base =
      I ∩ pullback.fst sZbar sX ⁻¹' Set.range j := himpre.symm.trans hL
  have hIcl : I = closure (Set.range (MMP.Flips.chowGraph hc.comp_eq hjc).base) := by
    rw [hGI]
    exact eq_closure_inter_preimage_of_forall_maximal_dense (pullback.fst sZbar sX).continuous
      hIc j.isOpenEmbedding.isOpen_range ⟨j s₀, s₀, rfl⟩ hIdom
  have hIirr : IsIrreducible I := hIcl ▸ hGirr.closure
  haveI : IsReduced Ubar.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  haveI : IrreducibleSpace Ubar.subscheme :=
    irreducibleSpace_subscheme_vanishingIdeal ⟨I, hIc⟩ hIirr
  haveI hUbint : IsIntegral Ubar.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  -- Step 8: `g : Ū ⟶ Z̄` is `f_U` over `Z₁`, so its fibres are connected (Stein)
  set g := Ubar.subschemeι ≫ pullback.fst sZbar sX with hg
  haveI : IsProper g := by rw [hg]; infer_instance
  haveI : QuasiCompact (MMP.Flips.chowGraph hc.comp_eq hjc ≫ pullback.fst sZbar sX ≫ sZbar) := by
    rw [MMP.Flips.chowGraph, pullback.lift_fst_assoc, Category.assoc, hjc]
    change QuasiCompact (π ≫ sS)
    infer_instance
  haveI : QuasiSeparated (pullback.fst sZbar sX ≫ sZbar) :=
    @IsSeparated.instQuasiSeparated _ _ _ inferInstance
  haveI : QuasiCompact (MMP.Flips.chowGraph hc.comp_eq hjc) :=
    QuasiCompact.of_comp _ (pullback.fst sZbar sX ≫ sZbar)
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : (fU ⁻¹ᵁ Z₁).toScheme ⟶ Ubar.subscheme,
      ψ' ≫ Ubar.subschemeι = MMP.Flips.chowGraph hc.comp_eq hjc := by
    refine ⟨IsClosedImmersion.lift _ _ ?_, IsClosedImmersion.lift_fac _ _ _⟩
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact MMP.Chow.FixedDegreeCurveCyclesProof.vanishingIdeal_le_ker_of_isReduced _ ⟨I, hIc⟩
      (hGI ▸ Set.inter_subset_left)
  haveI : Mono (MMP.Flips.chowGraph hc.comp_eq hjc) := by rw [hgraph]; infer_instance
  have hPB : IsPullback ψ' π g j :=
    isPullback_of_range_eq_inter_preimage_range Ubar.subschemeι (pullback.fst sZbar sX) j π _ ψ'
      hψ' (by rw [MMP.Flips.chowGraph, pullback.lift_fst]) (by rw [hGI, hIrange])
  haveI : IsIso π.c := isIso_c_morphismRestrict fU hc.isIso_app Z₁
  haveI := isIso_appTop_fiberToSpecResidueField_genericPoint hPB
  have hgsurj : Function.Surjective g := surjective_of_isPullback_of_dense_range hPB hπsurj
    (j.isOpenEmbedding.isOpen_range.dense ⟨j s₀, s₀, rfl⟩)
  have hgen : ∀ x : Ubar.subscheme, x ∈ genericPoints Ubar.subscheme →
      g x = genericPoint Zbar := by
    intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact genericPoint_map_of_surjective g hgsurj
  haveI : GeometricallyConnected g :=
    Stacks.SteinFactorization.geometricallyConnected_of_isNormal g hgen inferInstance
  -- Step 9: over a closed point `z̄`, the fibre of `Ū` is the support of the cycle of `z̄`
  haveI : JacobsonSpace 𝒞 := LocallyOfFiniteType.jacobsonSpace s𝒞
  have hu_img : ∀ z : Zbar, (Ubar.subschemeι ≫ pullback.snd sZbar sX).base ''
      (g.base ⁻¹' {z}) = pullback.snd sZbar sX '' (I ∩ pullback.fst sZbar sX ⁻¹' {z}) := by
    intro z
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, hg, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range, hIrange,
      Set.inter_comm]
  have hfibsupp : ∀ z : Zbar, IsClosed ({z} : Set Zbar) →
      (Ubar.subschemeι ≫ pullback.snd sZbar sX).base '' (g.base ⁻¹' {z}) =
        cycleSupport (cycOf (φbar z)) := by
    intro z hz
    rw [hu_img]
    exact snd_image_inter_fst_preimage_eq sZbar sX hIc (fun z => cycleSupport (cycOf (φbar z)))
      (fun z => (cycOf (φbar z)).support.finite_toSet.isClosed_biUnion fun C _ =>
        isClosed_closure) hIpts z hz
  -- Step 10: the curves in the fibres over closed points are `(K_X + Δ_X)`-trivial
  have hiii : ∀ z : Zbar, IsClosed ({z} : Set Zbar) → ∀ C : ProperCurve sX,
      closure {C.point} ⊆ (Ubar.subschemeι ≫ pullback.snd sZbar sX).base ''
        ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z}) →
      (Divisor.toQDivisor K + Δ).intersectionNumber k sX C.ι C.dim_le h.isQCartier = 0 := by
    intro z hz C hC
    change closure {C.point} ⊆ (Ubar.subschemeι ≫ pullback.snd sZbar sX).base ''
      (g.base ⁻¹' {z}) at hC
    rw [hfibsupp z hz] at hC
    have hcc : IsClosed ({φbar z} : Set 𝒞) := φbar.closePoints_subset_preimage_closedPoints hz
    haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
    have hz₀ : IsClosed ({Z₁.ι s₀} : Set Z) := Z₁.ι.closePoints_subset_preimage_closedPoints hs₀
    have hc₀ : IsClosed ({φ s₀} : Set 𝒞) := φ.closePoints_subset_preimage_closedPoints hs₀
    have hconn : φ s₀ ∈ connectedComponent (φbar z) :=
      (isConnected_range φbar.continuous).isPreconnected.subset_connectedComponent
        ⟨z, rfl⟩ ⟨j s₀, hφbarj s₀⟩
    refine intersectionNumber_eq_zero_of_mem_connectedComponent h cycOf
      (fun c hc => (hbij.mapsTo hc).1) hconst hcc hc₀ hconn (fun C' hC' => ?_)
      (mem_of_point_mem_curveUnion C (hC (subset_closure rfl)))
    have hsub : closure {C'.point} ⊆ U.ι '' (fU ⁻¹' {Z₁.ι s₀}) := by
      rw [← (hfibcyc s₀ hs₀).2, ← hφc s₀ hs₀]
      exact Set.subset_biUnion_of_mem (u := fun C => closure {C.point}) hC'
    exact htriv _ s₀.2 hz₀ C' hsub
  -- Step 11: only finitely many closed fibres lie in a given proper curve
  have hiv : ∀ S : Finset (ProperCurve sX), S.Nonempty →
      {z : Zbar | IsClosed ({z} : Set Zbar) ∧ (Ubar.subschemeι ≫ pullback.snd sZbar sX).base ''
        ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z}) ⊆ curveUnion sX S}.Finite :=
    fun S _ => finite_setOf_isClosed_subset_curveUnion i hbij φbar _ hfibsupp S
  -- Step 12: every component of every fibre of `g` is a curve
  set u := Ubar.subschemeι ≫ pullback.snd sZbar sX with hu
  have hgu : g ≫ sZbar = u ≫ sX := by
    rw [hg, hu, Category.assoc, Category.assoc, pullback.condition]
  have hliftι : pullback.lift g u hgu = Ubar.subschemeι := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hg]
    · rw [pullback.lift_snd, hu]
  haveI : IsClosedImmersion (pullback.lift g u hgu) := by rw [hliftι]; infer_instance
  haveI : LocallyOfFiniteType sZbar := hZbarnv.1.toLocallyOfFiniteType
  -- the dimensions of `Ū` and `Z̄`
  have hdimU₁ : topologicalKrullDim (fU ⁻¹ᵁ Z₁).toScheme = 3 := by
    rw [topologicalKrullDim_eq_of_isOpenImmersion sX ((fU ⁻¹ᵁ Z₁).ι ≫ U.ι)]
    exact h.dim_eq
  have hdimUbar : topologicalKrullDim Ubar.subscheme = 3 := by
    haveI : IrreducibleSpace (pullback g j : Scheme.{u}) :=
      (Scheme.homeoOfIso hPB.isoPullback).irreducibleSpace_iff.mp inferInstance
    rw [← topologicalKrullDim_eq_of_isOpenImmersion (g ≫ sZbar) (pullback.fst g j),
      ← (Scheme.homeoOfIso hPB.isoPullback).isHomeomorph.topologicalKrullDim_eq, hdimU₁]
  have hdimZbar : topologicalKrullDim Zbar = 2 := by
    rw [← topologicalKrullDim_eq_of_isOpenImmersion sZbar j,
      topologicalKrullDim_eq_of_isOpenImmersion sZ Z₁.ι]
    exact topologicalKrullDim_base_eq_two sX h.dim_eq U hU sZ fU hfU
  haveI : AlgebraicGeometry.IsVariety k (g ≫ sZbar) := AlgebraicGeometry.IsVariety.mk
  haveI : AlgebraicGeometry.IsVariety k sZbar := hZbarnv.1
  haveI : IsDominant g := ⟨hgsurj.denseRange⟩
  haveI : JacobsonSpace Ubar.subscheme := LocallyOfFiniteType.jacobsonSpace (g ≫ sZbar)
  have hdimfib' := topologicalKrullDim_eq_one_of_image_fiber_eq_cycleSupport g u hgu hdimUbar
    hdimZbar (fun z => cycOf (φbar z)) hfibsupp
  exact ⟨Z₁, Zbar, sZbar, j, Ubar,
    { satisfiesAbundanceAssumptions := h
      isLogEllipticFiberSpace := hfU
      nonempty_U := hU
      nonempty := hZ₁
      isNormalVariety := hZbarnv
      isProjectiveVariety := hZbarproj
      isOpenImmersion := inferInstance
      comp_eq := hjc
      isIntegral := hUbint
      image_preimage_eq := himpre
      isConnected_fiber := g.isConnected_preimage_singleton
      dim_fiber := hdimfib'
      intersectionNumber_eq_zero := hiii
      finite := hiv }⟩

/-- Existence of a Chow closure of `f_U`, through the Chow variety of curves of the fibre
degree. -/
private theorem exists_isChowClosure
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3 (DivisorWithCoeffs.restrict U.ι K)
      (DivisorWithCoeffs.restrict U.ι Δ) fU) :
    ∃ (Z₀ : Z.Opens) (Zbar : Scheme.{u}) (sZbar : Zbar ⟶ Spec (.of k))
        (j : Z₀.toScheme ⟶ Zbar) (Ubar : (pullback sZbar sX).IdealSheafData),
        IsChowClosure (sZ := sZ) (sZbar := sZbar) k sX K Δ fU Z₀ j Ubar := by
  obtain ⟨N, i, hi, rfl⟩ :=
    exists_isClosedImmersion_projToSpecCoeff h.isProjectiveVariety.isProjective
  exact exists_isChowClosure_of_isClosedImmersion i h U hU sZ fU hfU

end Construction

/-- **The Chow closure of the elliptic fibration** (FA, proof of 15.10). Let `(X, Δ_X)`, with
`K_X` a canonical divisor, satisfy the assumptions of 15.4
(`MMP.Flips.SatisfiesAbundanceAssumptions`) over an algebraically closed field `k` of
characteristic zero, and let `f_U : U ⟶ Z` be a log elliptic fiber space on a nonempty open
`U ⊆ X` as in (15.4.3). Then `f_U` has a Chow closure `(Z₀, Z̄, Ū)` (`MMP.Flips.IsChowClosure`),
and every Chow closure of `f_U` has `dim Z̄ = 2`. -/
@[mmp "lem_fa15_chow_closure_exists"]
public theorem exists_isChowClosure_and_dim_eq_two
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3 (DivisorWithCoeffs.restrict U.ι K)
      (DivisorWithCoeffs.restrict U.ι Δ) fU) :
    (∃ (Z₀ : Z.Opens) (Zbar : Scheme.{u}) (sZbar : Zbar ⟶ Spec (.of k))
        (j : Z₀.toScheme ⟶ Zbar) (Ubar : (pullback sZbar sX).IdealSheafData),
        IsChowClosure (sZ := sZ) (sZbar := sZbar) k sX K Δ fU Z₀ j Ubar) ∧
      ∀ (Z₀ : Z.Opens) (Zbar : Scheme.{u}) (sZbar : Zbar ⟶ Spec (.of k))
        (j : Z₀.toScheme ⟶ Zbar) (Ubar : (pullback sZbar sX).IdealSheafData),
        IsChowClosure (sZ := sZ) (sZbar := sZbar) k sX K Δ fU Z₀ j Ubar →
          topologicalKrullDim Zbar = 2 :=
  ⟨exists_isChowClosure sX h U hU sZ fU hfU,
    fun _ _ _ _ _ hc => topologicalKrullDim_eq_two_of_isChowClosure sX hc⟩

end MMP.Flips
