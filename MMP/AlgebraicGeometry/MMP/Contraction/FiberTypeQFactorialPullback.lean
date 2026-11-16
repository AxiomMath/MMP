module

public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.IndexOneCover
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.Positivity.FreeDivisorSteinFactorization
public import MMP.AlgebraicGeometry.Chow.FieldSituation

universe u

section

/-!
# The base of a fibre type contraction with the pullback property is `ℚ`-factorial

Let `X` be a `ℚ`-factorial normal projective variety, `R` an extremal ray of `NE̅(X)` and
`g : X ⟶ Z` a contraction of `R` with `dim Z < dim X`, such that every invertible sheaf of degree
zero on the curves of `R` is pulled back from `Z`. Then `Z` is `ℚ`-factorial.

For a Weil divisor `B` on `Z` let `D` be a divisor on `X` which is the pull-back `g^*B` over every
open of `Z` on which `B` has a local equation, and is zero along the prime divisors whose generic
points map outside these opens; `Supp D ⊆ g⁻¹(Supp B)`. Some multiple `mD` is Cartier. A fibre of
`g` over a closed point outside `Supp B` has positive dimension, so it contains a curve `C₀`, whose
class spans `R` and which misses `mD`; hence `𝒪_X(mD)` has degree zero on `R` and
`𝒪_X(mD) ≅ g^* 𝒪_Z(E)` for a Cartier divisor `E` on `Z`, so `mD - g^*E = div ψ`. Along every
prime divisor `P` of `Z`, `F = mB - E` has a local equation `f` near the generic point of `P`, and
`ψ / g^* f` has no zeros or poles over a neighbourhood `V` of it; by algebraic Hartogs it is a unit
on `g⁻¹ V`, hence (`g_* 𝒪_X = 𝒪_Z`) the pull-back of a unit on `V`. So `ψ = g^* φ` with
`v_P(φ) = F_P` for every `P`: `mB = E + div φ` is Cartier.

## Main results

* `MMP.Mori.isQFactorial_of_isFiberTypeContraction_of_forall_exists_iso_pullback`: the
  statement above.

## Implementation notes

The source restricts `B` to the smooth locus `Z⁰` and takes the closure of `g^*(B|_{Z⁰})`; here
`D` is instead the pull-back over every open on which `B` has a local equation
(`MMP.Mori.Divisor.IsPullback`, which needs no Cartier hypothesis), extended by zero; only the
generic points of the prime divisors of `Z`, near which every divisor on a normal scheme has a
local equation, are used. The injectivity of `g^* : Pic(Z⁰) → Pic(g⁻¹ Z⁰)` together with the
extension of the linear equivalence over `Z ∖ Z⁰` is replaced by the descent of `ψ` itself, which
gives the rational function `φ` with `mB - E = div φ` on all of `Z` at once.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.18
-/

open CategoryTheory AlgebraicGeometry MMP.Mori Topology TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.FourfoldProofs.Km3cFiberContractionQfactorialOverKProof

section Pullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y}

/-- **A pull-back of an arbitrary divisor over its local equations.** For a divisor `B` on `Y`
such that no generic point of an irreducible component of `X` maps into `Supp B`, there is a
divisor `B'` on `X` which is the pull-back of `B` in the sense of `MMP.Mori.Divisor.IsPullback`
(over every open on which `B` has a local equation) and whose components all map into
`Supp B`. -/
private theorem exists_isPullback (B : Divisor Y)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp) :
    ∃ B' : Divisor X, B.IsPullback f hB B' ∧
      ∀ E : MMP.Mori.PrimeDivisor X, B'.coeff E ≠ 0 → f E.genericPoint ∈ B.supp := by
  classical
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  set U₁ : Y.Opens := ⟨(B.supp : Set Y)ᶜ, B.supp.isClosed.isOpen_compl⟩
  have h1 : B.IsLocalEquation U₁ 1 := by
    rintro E ⟨y, hyE, hyU⟩
    rw [PrimeDivisor.ord_one]
    by_contra hne
    exact hyU (DivisorWithCoeffs.support_subset_supp hne hyE)
  let P : MMP.Mori.PrimeDivisor X → Prop := fun E => ∃ (U : Y.Opens) (φ : (RationalFunctions Y)ˣ),
    B.IsLocalEquation U φ ∧ (E.support ∩ f ⁻¹ᵁ U).Nonempty
  let c : MMP.Mori.PrimeDivisor X → ℤ := fun E => if h : P E then
    E.ordUnit (pullbackComponent f hB h.choose_spec.choose_spec.1 E.component
      (E.map_componentGenericPoint_mem f h.choose_spec.choose_spec.2)) else 0
  have hc : ∀ (U : Y.Opens) (φ : (RationalFunctions Y)ˣ) (hφ : B.IsLocalEquation U φ)
      (E : MMP.Mori.PrimeDivisor X) (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty),
      c E = E.ordUnit (pullbackComponent f hB hφ E.component
        (E.map_componentGenericPoint_mem f hE)) := by
    intro U φ hφ E hE
    have hP : P E := ⟨U, φ, hφ, hE⟩
    simp only [c, dif_pos hP]
    exact ordUnit_pullbackComponent_eq hB _ hφ E hP.choose_spec.choose_spec.2 hE
  have hc0 : ∀ E : MMP.Mori.PrimeDivisor X, c E ≠ 0 → f E.genericPoint ∈ B.supp := by
    intro E hE
    by_contra hnot
    have hE₁ : (E.support ∩ f ⁻¹ᵁ U₁).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U₁)).mp hnot
    apply hE
    rw [hc U₁ 1 h1 E hE₁, pullbackComponent_eq hB h1 _ (mem_pointComponent _) 1 (by simp),
      map_one, PrimeDivisor.ordUnit_one]
  have hT : ∀ s ∈ f ⁻¹' (B.supp : Set Y), Order.coheight s ≠ 0 := by
    intro s hs h0
    obtain ⟨W, hsW⟩ := exists_mem_irreducibleComponents s
    have hle : s ≤ componentGenericPoint X W :=
      (isGenericPoint_componentGenericPoint X W).specializes hsW
    have heq : s = componentGenericPoint X W :=
      (Specializes.antisymm (Order.coheight_eq_zero.mp h0 hle) hle).eq
    exact hB W (heq ▸ hs)
  have hfin : {E : MMP.Mori.PrimeDivisor X | c E ≠ 0}.Finite :=
    (finite_setOf_genericPoint_mem (B.supp.isClosed.preimage f.continuous) hT).subset hc0
  exact ⟨Finsupp.ofSupportFinite c hfin, hc, hc0⟩

end Pullback

section LocalEquation

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **A Weil divisor has a local equation near a codimension one point.** On a normal integral
locally Noetherian scheme every divisor `B` has a local equation on a neighbourhood of the
generic point of every prime divisor `P`: a power of a uniformizer of the discrete valuation
ring `𝒪_{Y,P}`, `P` being the only prime divisor through its generic point. -/
private theorem exists_isLocalEquation_genericPoint (B : Divisor Y)
    (P : MMP.Mori.PrimeDivisor Y) :
    ∃ (V : Y.Opens) (φ : (RationalFunctions Y)ˣ), P.genericPoint ∈ V ∧ B.IsLocalEquation V φ := by
  obtain ⟨t, ht⟩ := MMP.Positivity.PrimeDivisor.exists_ord_eq_one P
  obtain ⟨V, hV, hφ⟩ := MMP.Flips.exists_isLocalEquation_of_forall_ord_eq (t ^ B.coeff P)
    (x := P.genericPoint) fun E hE => by
      have hsp : E.genericPoint ⤳ P.genericPoint := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
        exact specializes_iff_mem_closure.mpr hE
      obtain rfl := MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes hsp
      rw [PrimeDivisor.ord_zpow, ht, smul_eq_mul, mul_one]
  exact ⟨V, _, hV, hφ⟩

end LocalEquation

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- On a projective variety the class `[C] ∈ N₁(X)` of a proper curve is nonzero: an ample
invertible sheaf has positive degree on `C`. -/
private theorem numericalClass_cycle_ne_zero (hX : MMP.Mori.IsProjectiveVariety k sX)
    (C : ProperCurve sX) : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  have hproj : IsProjectiveMorphism sX := hX.isProjective
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sX
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sX hproj.isHQuasiProjective)
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := inferInstance
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy sX L
    (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sX L hLa) C
    (fun _ _ => Subsingleton.elim _ _)
  intro h0
  have h := OneCycle.mem_numericallyTrivial.mp ((Submodule.Quotient.mk_eq_zero _).mp h0) L
  rw [OneCycle.degree_cycle] at h
  have : (0 : ℝ) < (degreeOn k sX C.ι C.dim_le L : ℝ) := by exact_mod_cast hpos
  exact this.ne' h

/-- **A curve in the fibre through a closed point where `f` is not quasi-finite.** For a proper
morphism `f` from a proper `k`-scheme and a closed point `x` at which `f` is not quasi-finite, the
fibre `f⁻¹(f(x))` has positive dimension, and it contains a proper curve contracted by `f`. -/
private theorem exists_properCurve_isContractedBy_of_not_quasiFiniteAt {Z : Scheme.{u}}
    [IsProper sX] [IsLocallyNoetherian X] {f : X ⟶ Z} [IsProper f] {x : X}
    (hxc : IsClosed ({x} : Set X)) (hx : ¬ f.QuasiFiniteAt x) :
    ∃ C : ProperCurve sX, C.IsContractedBy f ∧ f C.point = f x := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hy : IsClosed ({f x} : Set Z) := by
    simpa [Set.image_singleton] using f.isClosedMap _ hxc
  have hF : IsClosed (f ⁻¹' {f x}) := hy.preimage f.continuous
  have hdim : 0 < topologicalKrullDim (f ⁻¹' {f x}) := by
    by_contra! hle
    apply hx
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have h' : topologicalKrullDim (f.fiber (f x)) ≤ 0 := by
      rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo (f x)).isHomeomorph]
      exact hle
    have : IsLocallyNoetherian
        (CategoryTheory.Limits.pullback f (Z.fromSpecResidueField (f x))) := inferInstance
    have : IsLocallyNoetherian (f.fiber (f x)) := this
    have : IsLocallyArtinian (f.fiber (f x)) := IsLocallyArtinian.of_topologicalKrullDim_le_zero h'
    have : DiscreteTopology (f.fiber (f x)) :=
      (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mp inferInstance).2
    exact isOpen_discrete _
  rw [topologicalKrullDim, Order.krullDim_pos_iff] at hdim
  obtain ⟨A, B, hAB⟩ := hdim
  have hBirr : IsIrreducible (Subtype.val '' (B : Set (f ⁻¹' {f x}))) :=
    B.isIrreducible.image _ continuous_subtype_val.continuousOn
  set η := hBirr.genericPoint
  have hη : closure ({η} : Set X) = closure (Subtype.val '' (B : Set (f ⁻¹' {f x}))) :=
    hBirr.isGenericPoint_genericPoint_closure
  have hBF : closure (Subtype.val '' (B : Set (f ⁻¹' {f x}))) ⊆ f ⁻¹' {f x} :=
    closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact z.2) hF
  have hAcl : IsClosed (Subtype.val '' (A : Set (f ⁻¹' {f x}))) :=
    hF.isClosedEmbedding_subtypeVal.isClosedMap _ A.isClosed
  have hAne : (Subtype.val '' (A : Set (f ⁻¹' {f x}))).Nonempty :=
    A.isIrreducible.nonempty.image _
  obtain ⟨x₀, hx₀A, hx₀⟩ := hAcl.exists_closed_singleton hAne
  have hx₀B : x₀ ∈ closure (Subtype.val '' (B : Set (f ⁻¹' {f x}))) :=
    subset_closure (Set.image_mono hAB.le hx₀A)
  have hηx₀ : η ⤳ x₀ := specializes_iff_mem_closure.mpr (hη ▸ hx₀B)
  have hηne : η ∉ ({x₀} : Set X) := by
    intro hη₀
    rw [Set.mem_singleton_iff] at hη₀
    apply hAB.not_ge
    intro z hz
    have hz' : z.1 ∈ closure ({η} : Set X) := hη ▸ subset_closure ⟨z, hz, rfl⟩
    rw [hη₀, hx₀.closure_eq, Set.mem_singleton_iff] at hz'
    obtain ⟨a, ha, ha'⟩ := hx₀A
    have : z = a := Subtype.ext (hz'.trans ha'.symm)
    exact this ▸ ha
  obtain ⟨y', hηy', -, -, hcurve⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sX hηx₀ hx₀
    hx₀ (Set.mem_singleton _) hηne
  have hsub : closure ({y'} : Set X) ⊆ f ⁻¹' {f x} := by
    refine (closure_minimal (Set.singleton_subset_iff.mpr ?_) isClosed_closure).trans hBF
    exact hη ▸ specializes_iff_mem_closure.mp hηy'
  have h2 : f y' = f x := hsub (subset_closure rfl)
  exact ⟨⟨y', hcurve⟩, fun z hz => (hsub hz).trans h2.symm, h2⟩

/-- **A morphism lowering the dimension is not quasi-finite at the generic point.** For a dominant
morphism `g : X ⟶ Z` of `k`-schemes locally of finite type, `X` irreducible, with
`dim Z < dim X`, the generic fibre has dimension `dim X - dim Z > 0`; it is a Jacobson space, so
an open point of it would be closed, hence equal to the whole irreducible fibre. -/
private theorem not_quasiFiniteAt_genericPoint {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IrreducibleSpace X] [LocallyOfFiniteType sX] [LocallyOfFiniteType sZ] (g : X ⟶ Z)
    [IsDominant g] (hgs : g ≫ sZ = sX)
    (hdim : topologicalKrullDim Z < topologicalKrullDim X) :
    ¬ g.QuasiFiniteAt (genericPoint X) := by
  have : LocallyOfFiniteType g := MMP.Flips.locallyOfFiniteType_of_comp_eq sX sZ g hgs
  have hsum := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range g k sX sZ hgs
  rw [g.denseRange.closure_range,
    (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq] at hsum
  intro hqf
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber] at hqf
  have hcl : IsClosed ({g.asFiber (genericPoint X)} : Set (g.fiber (g (genericPoint X)))) :=
    isClosed_singleton_of_isLocallyClosed_singleton hqf.isLocallyClosed
  have huniv : ({g.asFiber (genericPoint X)} : Set (g.fiber (g (genericPoint X)))) = Set.univ := by
    rw [← hcl.closure_eq]
    exact g.isGenericPoint_asFiber_genericPoint
  have : Subsingleton (g.fiber (g (genericPoint X))) :=
    ⟨fun a b => by
      have ha : a ∈ ({g.asFiber (genericPoint X)} : Set _) := huniv ▸ Set.mem_univ a
      have hb : b ∈ ({g.asFiber (genericPoint X)} : Set _) := huniv ▸ Set.mem_univ b
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
  refine absurd hdim (not_lt.mpr ?_)
  rw [hsum]
  exact (add_le_add (topologicalKrullDim_zero_of_discreteTopology _) le_rfl).trans_eq
    (zero_add _)

/-- **A contracted curve over the complement of a closed set.** Let `g : X ⟶ Z` be a proper
dominant morphism from an irreducible proper `k`-scheme to a `k`-scheme locally of finite type
with `dim Z < dim X`, and `S ⊆ Z` a closed set missing the image of the generic point. Then there
is a proper curve contracted by `g` that lies over `Z ∖ S`. -/
private theorem exists_properCurve_isContractedBy_notMem {Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} [IrreducibleSpace X] [IsProper sX] [IsLocallyNoetherian X]
    [LocallyOfFiniteType sZ] (g : X ⟶ Z) [IsProper g] [IsDominant g] (hgs : g ≫ sZ = sX)
    (hdim : topologicalKrullDim Z < topologicalKrullDim X) {S : Set Z} (hS : IsClosed S)
    (hξ : g (genericPoint X) ∉ S) :
    ∃ C : ProperCurve sX, C.IsContractedBy g ∧ g C.point ∉ S := by
  have hnq := not_quasiFiniteAt_genericPoint g hgs hdim
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  obtain ⟨x, hxS, hxc⟩ := nonempty_inter_closedPoints (Z := g ⁻¹' Sᶜ) ⟨genericPoint X, hξ⟩
    (hS.isOpen_compl.preimage g.continuous).isLocallyClosed
  have hx : ¬ g.QuasiFiniteAt x := fun h => hnq <| by
    have hmem : x ∈ g.quasiFiniteLocus := Scheme.Hom.mem_quasiFiniteLocus.mpr h
    exact Scheme.Hom.mem_quasiFiniteLocus.mp
      ((genericPoint_specializes x).mem_open g.quasiFiniteLocus.isOpen hmem)
  obtain ⟨C, hC, hCx⟩ := exists_properCurve_isContractedBy_of_not_quasiFiniteAt (sX := sX) hxc hx
  exact ⟨C, hC, hCx ▸ hxS⟩

/-- **Degree zero along a ray.** If `R = ℝ_{≥0} · v` and an invertible sheaf `L` has degree zero
on a curve whose class lies in `R`, then `L` has degree zero on every curve with class in `R`. -/
private theorem degree_eq_zero_of_mem_ray (hX : MMP.Mori.IsProjectiveVariety k sX)
    {R : Set (NumericalCurveClasses sX)}
    (hR : ∃ v, v ≠ 0 ∧ R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {C₀ : ProperCurve sX}
    (hC₀ : OneCycle.numericalClass sX (C₀.cycle ℝ) ∈ R) (h0 : C₀.degree k L = 0) :
    ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R → C.degree k L = 0 := by
  obtain ⟨v, -, rfl⟩ := hR
  have hnum : ∀ C' : ProperCurve sX, (C'.degree k L : ℝ) =
      NumericalCurveClasses.degree sX L (OneCycle.numericalClass sX (C'.cycle ℝ)) := fun C' => by
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  obtain ⟨c₀, -, hc₀⟩ := hC₀
  have hc₀0 : c₀ ≠ 0 := fun h => numericalClass_cycle_ne_zero hX C₀ (by
    rw [← hc₀, h, zero_smul])
  have hv : NumericalCurveClasses.degree sX L v = 0 := by
    have h := hnum C₀
    rw [← hc₀, map_smul, h0, Int.cast_zero, smul_eq_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc₀0
  rintro C ⟨c, -, hcv⟩
  have h := hnum C
  rw [← hcv, map_smul, hv, smul_zero] at h
  exact_mod_cast h

/-- **A contracted curve missing the image of a Cartier divisor.** On a `ℚ`-factorial `X`, if
every component of a Cartier divisor `D` maps into a closed set `S` and a curve `C₀` contracted
by `g` lies over the complement of `S`, then `𝒪_X(D)` has degree zero on `C₀`. -/
private theorem degree_divisorialSheaf_eq_zero_of_isContractedBy [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (hQ : MMP.Fourfold.IsQFactorial sX) {Z : Scheme.{u}} {g : X ⟶ Z} {S : Set Z}
    (hS : IsClosed S) {D : Divisor X} (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule X D.divisorialSheaf]
    (hDS : ∀ E : MMP.Mori.PrimeDivisor X, D.coeff E ≠ 0 → g E.genericPoint ∈ S)
    {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy g) (hC₀S : g C₀.point ∉ S) :
    C₀.degree k D.divisorialSheaf = 0 := by
  have hQD : (Divisor.toQDivisor D).IsQCartier := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _
  have hdisj : ∀ x : X, C₀.point ⤳ x → x ∉ (Divisor.toQDivisor D).supp := by
    intro x hx hxD
    obtain ⟨E', hE'0, hxE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxD
    have hD0 : D.coeff E' ≠ 0 := fun h0 => hE'0 (by
      rw [Divisor.coeff_toQDivisor, h0, Int.cast_zero])
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE'
    refine hC₀S ?_
    rw [← hC₀ x (specializes_iff_mem_closure.mp hx)]
    exact ((specializes_iff_mem_closure.mpr hxE').map g.continuous).mem_closed hS (hDS E' hD0)
  have h := MMP.Fourfold.intersectionNumber_eq_zero_of_disjoint sX hQ _ hQD C₀ hdisj
  rw [QDivisor.intersectionNumber_toQDivisor k sX C₀.ι C₀.dim_le _ hD hQD] at h
  rw [ProperCurve.degree_divisorialSheaf C₀ _ hD]
  exact_mod_cast h

end Curves

section Descent

attribute [local instance] MMP.Resolution.componentField

variable {X Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {g : X ⟶ Z} [IsDominant g]

/-- **A unit with trivial divisor over `g⁻¹ V` is pulled back from `V`.** Let `g_* 𝒪_X = 𝒪_Z`.
If `χ ∈ K(X)^×` has order zero along every prime divisor meeting `g⁻¹ V`, `V` nonempty, then
`χ = g^* u` for a unit `u` of `Γ(Z, V)`: by algebraic Hartogs `χ` and `χ⁻¹` are regular on
`g⁻¹ V`, and `Γ(Z, V) ≅ Γ(X, g⁻¹ V)`. -/
private theorem exists_unit_fieldMap_germ_eq (hiso : ∀ U : Z.Opens, IsIso (g.app U))
    {V : Z.Opens} (χ : (RationalFunctions X)ˣ)
    (hχ : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ g ⁻¹ᵁ V).Nonempty → E.ord χ = 0)
    (ZZ : irreducibleComponents Z) (hZZ : componentGenericPoint Z ZZ ∈ V)
    (W : irreducibleComponents X) :
    ∃ a : Γ(Z, V)ˣ, MMP.Fourfold.fieldMap g ZZ W (Z.presheaf.germ V _ hZZ a) =
      (χ : RationalFunctions X) W := by
  have hW : componentGenericPoint X W ∈ g ⁻¹ᵁ V := by
    change g _ ∈ V
    rw [MMP.Fourfold.map_componentGenericPoint g W ZZ]
    exact hZZ
  have hsec : ∀ ξ : (RationalFunctions X)ˣ,
      (∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ g ⁻¹ᵁ V).Nonempty → E.ord ξ = 0) →
      ∃ s : Γ(X, g ⁻¹ᵁ V), X.presheaf.germ _ _ hW s = (ξ : RationalFunctions X) W := by
    intro ξ hξ
    obtain ⟨s, hs⟩ := (MMP.Fourfold.isDivisorialSection_of_unit (D := 0) ξ fun P hP => by
      rw [DivisorWithCoeffs.coeff_zero, hξ P hP, add_zero]).exists_eq
    exact ⟨s, congrFun hs ⟨W, hW⟩⟩
  obtain ⟨s, hs⟩ := hsec χ hχ
  obtain ⟨s', hs'⟩ := hsec χ⁻¹ fun E hE => by rw [PrimeDivisor.ord_inv, hχ E hE, neg_zero]
  have hss' : s * s' = 1 := germ_injective_of_isIntegral (X := X) _ hW (by
    rw [map_mul, hs, hs', map_one, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Pi.one_apply])
  let t : Γ(X, g ⁻¹ᵁ V)ˣ := ⟨s, s', hss', by rw [mul_comm]; exact hss'⟩
  let a : Γ(Z, V)ˣ := Units.map (inv (g.app V)).hom.toMonoidHom t
  refine ⟨a, ?_⟩
  have ha : (g.app V).hom (a : Γ(Z, V)) = s := by
    change (g.app V).hom ((inv (g.app V)).hom s) = s
    simp
  rw [MMP.Fourfold.fieldMap_germ g ZZ W hZZ, ha, hs]

/-- **Descent of a principal divisor along a contraction.** Let `g : X ⟶ Z` be a dominant
morphism of normal integral Noetherian schemes with `g_* 𝒪_X = 𝒪_Z`, `F` a divisor on `Z` and
`ψ ∈ K(X)^×`. Suppose that near the generic point of every prime divisor of `Z`, `F` has a local
equation `φ` on an open `V` with `div ψ = g^* div φ` over `g⁻¹ V`. Then `F` is principal: over
`V`, `ψ / g^* φ` is the pull-back of a unit `u` of `Γ(Z, V)`, so `ψ = g^*(u φ)`, and the rational
function `u φ`, independent of `V` since `g^*` is injective on function fields, has order `F_P`
along every prime divisor `P`. -/
private theorem exists_eq_principalDivisor [CompactSpace Z]
    (hiso : ∀ U : Z.Opens, IsIso (g.app U)) (F : Divisor Z)
    (hF : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ F.supp)
    (ψ : (RationalFunctions X)ˣ)
    (h : ∀ P : MMP.Mori.PrimeDivisor Z, ∃ (V : Z.Opens) (φ : (RationalFunctions Z)ˣ)
      (hφ : F.IsLocalEquation V φ), P.genericPoint ∈ V ∧
      ∀ (E : MMP.Mori.PrimeDivisor X) (hE : (E.support ∩ g ⁻¹ᵁ V).Nonempty),
        E.ord ψ = E.ordUnit
          (pullbackComponent g hF hφ E.component (E.map_componentGenericPoint_mem g hE))) :
    ∃ θ : (RationalFunctions Z)ˣ, F = principalDivisor θ := by
  have hsubZ := MMP.Fourfold.subsingleton_irreducibleComponents (X := Z)
  obtain ⟨ZZ⟩ : Nonempty (irreducibleComponents Z) := ⟨pointComponent (genericPoint Z)⟩
  obtain ⟨W⟩ : Nonempty (irreducibleComponents X) := ⟨pointComponent (genericPoint X)⟩
  have key : ∀ P : MMP.Mori.PrimeDivisor Z, ∃ θ : (RationalFunctions Z)ˣ,
      MMP.Fourfold.fieldMap g ZZ W ((θ : RationalFunctions Z) ZZ) = (ψ : RationalFunctions X) W ∧
      F.coeff P = P.ord θ := by
    intro P
    obtain ⟨V, φ, hφ, hP, hψ⟩ := h P
    have hPV : (P.support ∩ V).Nonempty := (P.genericPoint_mem_iff V).mp hP
    have hZZ' : ∀ Z' : irreducibleComponents Z, componentGenericPoint Z Z' ∈ V := fun Z' => by
      obtain rfl := Subsingleton.elim Z' P.component
      exact P.componentGenericPoint_mem_of_nonempty hPV
    have hZZ := hZZ' ZZ
    have hV : ∀ W' : irreducibleComponents X, g (componentGenericPoint X W') ∈ V := fun W' => by
      rw [MMP.Fourfold.map_componentGenericPoint g W' ZZ]
      exact hZZ
    let ρ : ∀ W' : irreducibleComponents X, (X.presheaf.stalk (componentGenericPoint X W'))ˣ :=
      fun W' => pullbackComponent g hF hφ W' (hV W')
    let χ : (RationalFunctions X)ˣ := ψ * (RationalFunctions.unitsEquiv X).symm fun W' => (ρ W')⁻¹
    have hχ : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ g ⁻¹ᵁ V).Nonempty → E.ord χ = 0 := by
      intro E hE
      have h1 : Units.map (RationalFunctions.component X E.component).toMonoidHom
          ((RationalFunctions.unitsEquiv X).symm fun W' => (ρ W')⁻¹) = (ρ E.component)⁻¹ := by
        ext
        rfl
      rw [PrimeDivisor.ord_mul, hψ E hE,
        PrimeDivisor.ord_eq_ordUnit _ ((RationalFunctions.unitsEquiv X).symm _), h1,
        ← zpow_neg_one, PrimeDivisor.ordUnit_zpow]
      ring
    obtain ⟨a, ha⟩ := exists_unit_fieldMap_germ_eq hiso χ hχ ZZ hZZ W
    let θ₀ : (RationalFunctions Z)ˣ := (RationalFunctions.unitsEquiv Z).symm fun Z' =>
      Units.map (Z.presheaf.germ V (componentGenericPoint Z Z') (hZZ' Z')).hom.toMonoidHom a
    refine ⟨θ₀ * φ, ?_, ?_⟩
    · change MMP.Fourfold.fieldMap g ZZ W
        (Z.presheaf.germ V _ (hZZ' ZZ) a * (φ : RationalFunctions Z) ZZ) = _
      rw [map_mul, ha, ← MMP.Fourfold.pullbackComponent_eq_fieldMap g hF hφ W (hV W) ZZ]
      change (ψ : RationalFunctions X) W * ((ρ W)⁻¹ : (X.presheaf.stalk _)ˣ) * (ρ W) = _
      rw [mul_assoc, Units.inv_mul, mul_one]
    · have hθ₀ : P.ord θ₀ = 0 := by
        refine P.ord_eq_zero_of_isUnit (a := Z.presheaf.germ V P.genericPoint hP a)
          (a.isUnit.map _) ?_
        change (Z.presheaf.stalkSpecializes _).hom (Z.presheaf.germ V P.genericPoint hP a) =
          Z.presheaf.germ V _ (hZZ' P.component) a
        exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
      rw [PrimeDivisor.ord_mul, hθ₀, zero_add, hφ P hPV]
  by_cases hne : Nonempty (MMP.Mori.PrimeDivisor Z)
  · obtain ⟨P₀⟩ := hne
    obtain ⟨θ₀, hθ₀, -⟩ := key P₀
    refine ⟨θ₀, Finsupp.ext fun P => ?_⟩
    obtain ⟨θ, hθ, hP⟩ := key P
    have hθθ₀ : θ = θ₀ := by
      refine Units.ext (funext fun Z' => ?_)
      obtain rfl := Subsingleton.elim Z' ZZ
      exact (MMP.Fourfold.fieldMap g Z' W).injective (hθ.trans hθ₀.symm)
    change F.coeff P = (principalDivisor θ₀).coeff P
    rw [hP, hθθ₀, coeff_principalDivisor]
  · exact ⟨1, Finsupp.ext fun P => absurd ⟨P⟩ hne⟩

/-- **Local equations of `mB - E` matching `ψ`.** Let `D` be the pull-back of `B` over its local
equations, `E` Cartier and `mD - g^*E = div ψ`. Near the generic point of every prime divisor `P`
of `Z`, `mB - E` has a local equation `φ` on an open `V` with `div ψ = g^* div φ` over
`g⁻¹ V`. -/
private theorem exists_isLocalEquation_ord_eq
    (hgen : ∀ (G : Divisor Z) (W : irreducibleComponents X), g (componentGenericPoint X W) ∉ G.supp)
    {B : Divisor Z} {D : Divisor X} (hD : B.IsPullback g (hgen B) D) {E : Divisor Z}
    (hEc : E.IsCartier) (m : ℤ) {ψ : (RationalFunctions X)ˣ}
    (hψ : m • D - E.pullback hEc (hgen E) = principalDivisor ψ) (P : MMP.Mori.PrimeDivisor Z) :
    ∃ (V : Z.Opens) (φ : (RationalFunctions Z)ˣ) (hφ : (m • B - E).IsLocalEquation V φ),
      P.genericPoint ∈ V ∧
        ∀ (E' : MMP.Mori.PrimeDivisor X) (hE' : (E'.support ∩ g ⁻¹ᵁ V).Nonempty),
        E'.ord ψ = E'.ordUnit
          (pullbackComponent g (hgen _) hφ E'.component
            (E'.map_componentGenericPoint_mem g hE')) := by
  obtain ⟨V₁, φ₁, hP₁, hφ₁⟩ := exists_isLocalEquation_genericPoint B P
  obtain ⟨V₂, hP₂, φ₂, hφ₂⟩ := hEc P.genericPoint
  have hφ₁m : (m • B).IsLocalEquation (V₁ ⊓ V₂) (φ₁ ^ m) := (hφ₁.mono inf_le_left).zsmul _
  have hφ₂n : ((-1 : ℤ) • E).IsLocalEquation (V₁ ⊓ V₂) (φ₂ ^ (-1 : ℤ)) :=
    (hφ₂.mono inf_le_right).zsmul _
  have hφ : (m • B - E).IsLocalEquation (V₁ ⊓ V₂) (φ₁ ^ m * φ₂ ^ (-1 : ℤ)) := by
    have := hφ₁m.add hφ₂n
    rwa [neg_one_zsmul, ← sub_eq_add_neg] at this
  refine ⟨V₁ ⊓ V₂, _, hφ, ⟨hP₁, hP₂⟩, fun E' hE' => ?_⟩
  have hE'₁ : (E'.support ∩ g ⁻¹ᵁ V₁).Nonempty :=
    hE'.mono (Set.inter_subset_inter_right _ fun x hx => hx.1)
  have hE'₂ : (E'.support ∩ g ⁻¹ᵁ V₂).Nonempty :=
    hE'.mono (Set.inter_subset_inter_right _ fun x hx => hx.2)
  have hZ := E'.map_componentGenericPoint_mem g hE'
  rw [pullbackComponent_mul (hgen _) (hgen (m • B)) (hgen ((-1 : ℤ) • E)) hφ hφ₁m hφ₂n hZ hZ hZ,
    pullbackComponent_zpow (hgen _) (hgen B) _ hφ₁m hφ₁ hZ
      (E'.map_componentGenericPoint_mem g hE'₁),
    pullbackComponent_zpow (hgen _) (hgen E) _ hφ₂n hφ₂ hZ
      (E'.map_componentGenericPoint_mem g hE'₂),
    PrimeDivisor.ordUnit_mul, PrimeDivisor.ordUnit_zpow, PrimeDivisor.ordUnit_zpow,
    ← hD V₁ φ₁ hφ₁ E' hE'₁, ← Divisor.isPullback_pullback hEc (hgen E) V₂ φ₂ hφ₂ E' hE'₂]
  have := congrArg (fun G : Divisor X => G.coeff E') hψ
  simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
    coeff_principalDivisor, smul_eq_mul] at this
  rw [← this]
  ring

end Descent

end MMP.FourfoldProofs.Km3cFiberContractionQfactorialOverKProof

end

section

/-!
# Fibre type contractions with the pullback property preserve `ℚ`-factoriality

Let `X` be a normal projective `ℚ`-factorial variety over an algebraically closed field `k` of
characteristic zero, `R` an extremal ray of the closed cone of curves `NE̅(X)` and `g : X ⟶ Z` a
contraction of `R` of fibre type, i.e. with `dim Z < dim X`. Suppose that `(R, g)` has the
*pullback property*: every invertible sheaf `L` on `X` with `(L · C) = 0` for every irreducible
curve `C` with `[C] ∈ R` is isomorphic to `g^* L_Z` for an invertible sheaf `L_Z` on `Z`. Then
`Z` is `ℚ`-factorial.

No singularity hypothesis on `X` beyond normality and no negativity of `R` is assumed: the
pullback property replaces the descent theorem for line bundles, which is where such hypotheses
enter in `MMP.Mori.isQFactorial_of_isFiberTypeContraction`.

## Main results

* `MMP.Mori.isQFactorial_of_isFiberTypeContraction_of_forall_exists_iso_pullback`: the
  statement above.

## Implementation notes

The fibre type contraction is `MMP.Mori.IsFiberTypeContraction`, which carries the normality of
`X`, the extremality of `R`, the contraction `MMP.Mori.IsContractionOfFace` and the inequality
of dimensions. `ℚ`-factoriality is `MMP.Fourfold.IsQFactorial`, which is stated for a locally
noetherian normal scheme; these two properties of `Z` follow from `Z` being the target of a
contraction of a normal projective variety, and are taken as instance arguments so that Weil
divisors on `Z` make sense in the statement. An irreducible curve is a `MMP.Mori.ProperCurve`,
`(L · C)` is `MMP.Mori.ProperCurve.degree`, and `g^*` is
`AlgebraicGeometry.Scheme.Modules.pullback g`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.18
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology
  MMP.FourfoldProofs.Km3cFiberContractionQfactorialOverKProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **The base of a fibre type contraction with the pullback property is `ℚ`-factorial**
(Kollár–Mori 3.18). Let `X` be a `ℚ`-factorial normal projective variety over an algebraically
closed field `k` of characteristic zero and `g : X ⟶ Z` a fibre type contraction of an extremal
ray `R` of `NE̅(X)` such that every invertible sheaf on `X` of degree `0` on every curve with
class in `R` is the pullback along `g` of an invertible sheaf on `Z`. Then `Z` is
`ℚ`-factorial. -/
@[mmp "lem_km3c_fiber_contraction_qfactorial_over_k"]
public theorem isQFactorial_of_isFiberTypeContraction_of_forall_exists_iso_pullback
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [hXv : AlgebraicGeometry.IsProjectiveVariety k sX]
    (hQ : MMP.Fourfold.IsQFactorial sX) {R : Set (NumericalCurveClasses sX)}
    {Z : Scheme.{0}} [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}
    (hg : IsFiberTypeContraction k sX sZ R g)
    (hpb : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      (∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R → C.degree k L = 0) →
      ∃ LZ : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback g).obj LZ)) :
    MMP.Fourfold.IsQFactorial sZ := by
  have hc := hg.isContractionOfFace
  have hZv : AlgebraicGeometry.IsProjectiveVariety k sZ := hc.isProjectiveVariety_target
  have hZv' := (AlgebraicGeometry.isProjectiveVariety_iff k sZ).mp hZv
  have hXv' := (AlgebraicGeometry.isProjectiveVariety_iff k sX).mp hXv
  have : IsIntegral Z := hZv'.1.toIsIntegral
  have : IsSeparated sZ := hZv'.1.toIsSeparated
  have : LocallyOfFiniteType sZ := hZv'.1.toLocallyOfFiniteType
  have : QuasiCompact sZ := hZv'.1.toQuasiCompact
  have : IsProper sX := isProper_of_isProjectiveMorphism _ hXv'.2
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsProper (g ≫ sZ) := hc.comp_eq ▸ inferInstance
  have : IsProper g := IsProper.of_comp g sZ
  have : Surjective g := g.surjective_of_isIso_app hc.isIso_app
  refine ⟨⟨hZv'.1, inferInstance⟩, fun B => ?_⟩
  have hgen : ∀ G : Divisor Z, ∀ W : irreducibleComponents X,
      g (componentGenericPoint X W) ∉ G.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g
  obtain ⟨D, hD, hDsupp⟩ := exists_isPullback B (hgen B)
  obtain ⟨m, hm, hmD⟩ := hQ.2 D
  have := hmD.isInvertibleModule_divisorialSheaf
  have hξ : g (genericPoint X) ∉ (B.supp : Set Z) := by
    have := hgen B (pointComponent (genericPoint X))
    rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this
  obtain ⟨C₀, hC₀, hC₀S⟩ := exists_properCurve_isContractedBy_notMem (sX := sX) g hc.comp_eq
    hg.dim_lt B.supp.isClosed hξ
  have hdeg0 := degree_divisorialSheaf_eq_zero_of_isContractedBy hQ B.supp.isClosed hmD
    (fun E hE => hDsupp E fun h => hE (by rw [DivisorWithCoeffs.coeff_smul, h, smul_zero])) hC₀ hC₀S
  obtain ⟨M, hM, ⟨e⟩⟩ := hpb _ (degree_eq_zero_of_mem_ray hXv hg.isExtremalRay.2 _
    ((hc.isContractedBy_iff C₀).mp hC₀) hdeg0)
  obtain ⟨E, hEc, ⟨eE⟩⟩ := exists_isCartier_divisorialSheaf_iso_of_isInvertible M
  obtain ⟨eP⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hEc g (hgen E)
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback g).mapIso eE.symm ≪≫ eP.symm)
  obtain ⟨θ, hθ⟩ := exists_eq_principalDivisor hc.isIso_app ((m : ℤ) • B - E)
    (hgen _) ψ (exists_isLocalEquation_ord_eq hgen hD hEc _ hψ)
  refine ⟨m, hm, ?_⟩
  have : (m : ℤ) • B = principalDivisor θ + E := by rw [← hθ]; abel
  rw [this]
  exact (Divisor.isCartier_principalDivisor θ).add hEc

end MMP.Mori

end
