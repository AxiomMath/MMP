module

public import MMP.AlgebraicGeometry.Divisor.OrderPullback
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Stalks
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace MMP.Intersection

variable {X Y : Scheme.{u}}

/-! ### Units near a point -/

/-- A section of a presheaf of rings whose germ at `x` is a unit is a unit near `x`. -/
theorem exists_isUnit_map_of_isUnit_germ {T : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} T)
    {U : Opens T} {x : T} (hx : x ∈ U) (s : F.obj (op U)) (hs : IsUnit (F.germ U x hx s)) :
    ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧ IsUnit (F.map (homOfLE hVU).op s) := by
  obtain ⟨W, hxW, t, ht⟩ := F.exists_germ_eq (↑hs.unit⁻¹ : F.stalk x)
  have hxUW : x ∈ U ⊓ W := ⟨hx, hxW⟩
  have h1 : F.germ (U ⊓ W) x hxUW
      (F.map (homOfLE inf_le_left).op s * F.map (homOfLE inf_le_right).op t) =
      F.germ (U ⊓ W) x hxUW 1 := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply F (homOfLE inf_le_left) x hxUW s,
      TopCat.Presheaf.germ_res_apply F (homOfLE inf_le_right) x hxUW t, ht, map_one]
    exact hs.mul_val_inv
  obtain ⟨V, hxV, i, j, hij⟩ := F.germ_eq x _ _ _ _ h1
  refine ⟨V, i.le.trans inf_le_left, hxV, ?_⟩
  rw [map_one, map_mul] at hij
  refine IsUnit.of_mul_eq_one (F.map i.op (F.map (homOfLE inf_le_right).op t)) ?_
  rw [← hij]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  rfl

/-- On a locally Noetherian scheme, a non-zero-divisor of `𝒪_{X,x}` is a unit of `𝓜_{X,x}`. -/
theorem isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors [IsLocallyNoetherian X] {x : X}
    {c : X.presheaf.stalk x} (hc : c ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    IsUnit (stalkToTotalQuotient x c) := by
  rw [← regularSectionGerms_eq_nonZeroDivisors_of_isLocallyNoetherian X x] at hc
  let T : Submonoid (X.presheaf.stalk x) :=
    (IsUnit.submonoid _).comap (stalkToTotalQuotient x).toMonoidHom
  have hle : (⨆ (U : Opens X) (hx : x ∈ U), ((X.presheaf.submonoidPresheafOfStalk
      (fun y ↦ nonZeroDivisors (X.presheaf.stalk y))).obj (op U)).map
        (X.presheaf.germ U x hx).hom) ≤ T := by
    refine iSup_le fun U => iSup_le fun hx => ?_
    rintro z ⟨s, hs, rfl⟩
    change s ∈ ⨅ y : U, Submonoid.comap (X.presheaf.germ U y.1 y.2).hom
      (nonZeroDivisors (X.presheaf.stalk y)) at hs
    have hu := isUnit_toTotalQuotientSheaf_app X.sheaf U s
      (fun y hy => Submonoid.mem_iInf.mp hs ⟨y, hy⟩)
    change IsUnit (stalkToTotalQuotient x _)
    rw [← germ_toTotalQuotient]
    exact hu.map _
  exact hle hc

/-! ### Local equations from germs, and gluing -/

/-- A unit of `Γ(V, 𝓜_X)` whose germ at every point of `V` is a local equation of `D` is a local
equation of `D` on `V`. -/
theorem isLocalEquationOn_of_forall_isLocalEquationAt {D : X.CartierDivisor} {V : X.Opens}
    {G : (X.totalQuotientSheaf.obj.obj (op V))ˣ}
    (h : ∀ (p : X) (hp : p ∈ V),
      IsLocalEquationAt D p (X.totalQuotientSheaf.presheaf.germ V p hp (G : _))) :
    IsLocalEquationOn D V G := by
  apply isLocalEquationOn_of_locally
  intro p hp
  obtain ⟨U, hpU, g, hg, hgG⟩ := h p hp
  obtain ⟨W, hpW, i, j, hij⟩ :=
    X.totalQuotientSheaf.presheaf.germ_eq p hpU hp (g : _) (G : _) hgG
  refine ⟨W, j, hpW, ?_⟩
  rw [show resUnit j G = resUnits i.le g from Units.ext hij.symm]
  exact hg.res i.le

/-- The image of a unit of `𝒪_{X,p}` is a local equation of the zero divisor at `p`. -/
theorem isLocalEquationAt_zero_stalkToTotalQuotient (p : X) (w : (X.presheaf.stalk p)ˣ) :
    IsLocalEquationAt (0 : X.CartierDivisor) p (stalkToTotalQuotient p w) := by
  have h0 : p ∉ cartierSupport (0 : X.CartierDivisor) := by
    rw [germ_cartierSupport_eq_zero_iff]
    exact map_zero _
  simpa using (isLocalEquationAt_one_of_notMem_cartierSupport h0).mul_units w

/-- Units `Gᵢ ∈ Γ(Wᵢ, 𝓜_X^*)` on an open cover whose germs at every common point differ by units of
the local ring are the local equations of a Cartier divisor. -/
theorem exists_isLocalEquationOn_of_germ_eq_mul {ι : Type*} (W : ι → X.Opens) (hW : iSup W = ⊤)
    (G : ∀ i, (X.totalQuotientSheaf.obj.obj (op (W i)))ˣ)
    (hG : ∀ i j (p : X) (hi : p ∈ W i) (hj : p ∈ W j), ∃ w : (X.presheaf.stalk p)ˣ,
      X.totalQuotientSheaf.presheaf.germ (W j) p hj (G j : _) =
        X.totalQuotientSheaf.presheaf.germ (W i) p hi (G i : _) * stalkToTotalQuotient p w) :
    ∃ D : X.CartierDivisor, ∀ i, IsLocalEquationOn D (W i) (G i) := by
  have hc : TopCat.Presheaf.IsCompatible (cartierSheaf X).obj W
      (fun i => cartierClass (W i) (G i)) := by
    intro i j
    change (cartierSheaf X).obj.map (homOfLE inf_le_left).op _ =
      (cartierSheaf X).obj.map (homOfLE inf_le_right).op _
    rw [← cartierClass_resUnit, ← cartierClass_resUnit]
    have h0 : IsLocalEquationOn (0 : X.CartierDivisor) (W i ⊓ W j)
        ((resUnits (inf_le_left : W i ⊓ W j ≤ W i) (G i))⁻¹ *
          resUnits (inf_le_right : W i ⊓ W j ≤ W j) (G j)) := by
      apply isLocalEquationOn_of_forall_isLocalEquationAt
      intro p hp
      obtain ⟨w, hw⟩ := hG i j p hp.1 hp.2
      have hw' : germUnits hp.2 (G j) =
          germUnits hp.1 (G i) * Units.map (stalkToTotalQuotient p).toMonoidHom w :=
        Units.ext hw
      have key : germUnits hp ((resUnits (inf_le_left : W i ⊓ W j ≤ W i) (G i))⁻¹ *
          resUnits (inf_le_right : W i ⊓ W j ≤ W j) (G j)) =
          Units.map (stalkToTotalQuotient p).toMonoidHom w := by
        rw [map_mul, map_inv, germUnits_res, germUnits_res, hw', inv_mul_cancel_left]
      have := isLocalEquationAt_zero_stalkToTotalQuotient p w
      rwa [show stalkToTotalQuotient p (w : X.presheaf.stalk p) =
        ((Units.map (stalkToTotalQuotient p).toMonoidHom w : _ˣ) : _) from rfl, ← key] at this
    unfold IsLocalEquationOn at h0
    rwa [restrictDivisor_zero, cartierClass_mul, cartierClass_inv, neg_add_eq_zero] at h0
  obtain ⟨D, hD, -⟩ := TopCat.Sheaf.existsUnique_gluing' (cartierSheaf X) W ⊤
    (fun _ => homOfLE le_top) hW.ge _ hc
  exact ⟨D, fun i => (hD i).symm⟩

/-! ### Local rings at generizations -/

/-- A section on an affine open avoids the prime of a point exactly when that point lies in the
basic open set of the section. -/
theorem notMem_primeIdealOf_iff_mem_basicOpen {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (r : Γ(X, U)) :
    r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔ x ∈ X.basicOpen r := by
  change hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen r ↔ _
  rw [← hU.fromSpec_preimage_basicOpen]
  change hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen r ↔ _
  rw [hU.fromSpec_primeIdealOf]

/-- The specialization map `𝒪_{X,x} → 𝒪_{X,x'}` along `x' ⤳ x` sends a germ to a unit exactly
when `x'` lies in the basic open set of a representing section. -/
theorem isUnit_stalkSpecializes_germ_iff {x' x : X} (h : x' ⤳ x) {U : X.Opens} (hxU : x ∈ U)
    (r : Γ(X, U)) :
    IsUnit (X.presheaf.stalkSpecializes h (X.presheaf.germ U x hxU r)) ↔
      x' ∈ X.basicOpen r := by
  rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes,
    X.mem_basicOpen r x' (h.mem_open U.isOpen hxU)]

/-- For `x' ⤳ x`, the local ring `𝒪_{X,x'}` is the localization of `𝒪_{X,x}` at the prime
`𝔭 = (sp)⁻¹ 𝔪_{x'}` of `x'`. -/
theorem isLocalization_stalkSpecializes {x' x : X} (h : x' ⤳ x) :
    letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk x')
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk x')).comap
        (X.presheaf.stalkSpecializes h).hom) := by
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have hP : ∀ a : X.presheaf.stalk x, a ∈ ((IsLocalRing.maximalIdeal
      (X.presheaf.stalk x')).comap (X.presheaf.stalkSpecializes h).hom).primeCompl ↔
      IsUnit (X.presheaf.stalkSpecializes h a) := by
    intro a
    change ¬ (_ ∈ IsLocalRing.maximalIdeal _) ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hzero (a : X.presheaf.stalk x) (ha : X.presheaf.stalkSpecializes h a = 0) :
      ∃ c : ((IsLocalRing.maximalIdeal (X.presheaf.stalk x')).comap
        (X.presheaf.stalkSpecializes h).hom).primeCompl, c * a = 0 := by
    obtain ⟨U, hxU, hU, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens X.presheaf x a
    have hηU : x' ∈ U := h.mem_open U.isOpen hxU
    let := (X.presheaf.germ U x' hηU).hom.toAlgebra
    let := hU.isLocalization_stalk ⟨x', hηU⟩
    have hs : algebraMap Γ(X, U) (X.presheaf.stalk x') s =
        algebraMap Γ(X, U) (X.presheaf.stalk x') 0 := by
      change X.presheaf.germ U x' hηU s = X.presheaf.germ U x' hηU 0
      simpa only [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes,
        map_zero] using ha
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
      (M := (hU.primeIdealOf ⟨x', hηU⟩).asIdeal.primeCompl) hs
    have hηc : x' ∈ X.basicOpen (c : Γ(X, U)) :=
      (notMem_primeIdealOf_iff_mem_basicOpen hU hηU c).mp c.2
    refine ⟨⟨X.presheaf.germ U x hxU c,
      (hP _).2 ((isUnit_stalkSpecializes_germ_iff h hxU c).2 hηc)⟩, ?_⟩
    change X.presheaf.germ U x hxU c * X.presheaf.germ U x hxU s = 0
    simpa only [map_mul, mul_zero, map_zero] using
      congrArg (fun a : Γ(X, U) => X.presheaf.germ U x hxU a) hc
  refine { map_units := fun r => (hP r).1 r.2, surj := ?_, exists_of_eq := ?_ }
  · intro a
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hηU : x' ∈ U := h.mem_open U.isOpen hxU
    let := (X.presheaf.germ U x' hηU).hom.toAlgebra
    let := hU.isLocalization_stalk ⟨x', hηU⟩
    obtain ⟨⟨s, r⟩, hr⟩ := IsLocalization.surj
      (hU.primeIdealOf ⟨x', hηU⟩).asIdeal.primeCompl a
    have hηr : x' ∈ X.basicOpen (r : Γ(X, U)) :=
      (notMem_primeIdealOf_iff_mem_basicOpen hU hηU r).mp r.2
    refine ⟨⟨X.presheaf.germ U x hxU s,
      ⟨X.presheaf.germ U x hxU r, (hP _).2 ((isUnit_stalkSpecializes_germ_iff h hxU r).2 hηr)⟩⟩,
      ?_⟩
    change a * X.presheaf.stalkSpecializes h (X.presheaf.germ U x hxU r) =
      X.presheaf.stalkSpecializes h (X.presheaf.germ U x hxU s)
    change a * X.presheaf.germ U x' hηU r = X.presheaf.germ U x' hηU s at hr
    simpa only [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] using hr
  · intro a b hab
    change X.presheaf.stalkSpecializes h a = X.presheaf.stalkSpecializes h b at hab
    obtain ⟨c, hc⟩ := hzero (a - b) (by simp only [map_sub, hab, sub_self])
    exact ⟨c, sub_eq_zero.mp (by simpa only [mul_sub] using hc)⟩

/-- The point `η` of `X` given by a prime `𝔮` of `𝒪_{X,y}` (the image of `𝔮` under
`Spec 𝒪_{X,y} → X`) specializes to `y`. -/
theorem fromSpecStalk_specializes (y : X) (q : PrimeSpectrum (X.presheaf.stalk y)) :
    X.fromSpecStalk y q ⤳ y := by
  have h : X.fromSpecStalk y q ∈ Set.range (X.fromSpecStalk y) := ⟨q, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at h

/-- The point of a prime `𝔮` of `𝒪_{X,y}` lies in the basic open set of a section exactly when the
germ of the section avoids `𝔮`. -/
theorem fromSpecStalk_mem_basicOpen_iff {y : X} {U : X.Opens} (hyU : y ∈ U) (r : Γ(X, U))
    (q : PrimeSpectrum (X.presheaf.stalk y)) :
    X.fromSpecStalk y q ∈ X.basicOpen r ↔ X.presheaf.germ U y hyU r ∉ q.asIdeal := by
  change q ∈ (X.fromSpecStalk y) ⁻¹ᵁ X.basicOpen r ↔ _
  rw [Scheme.preimage_basicOpen, Scheme.fromSpecStalk_app hyU]
  simp only [CommRingCat.comp_apply, Scheme.basicOpen_res, basicOpen_eq_of_affine]
  exact ⟨fun h => h.2, fun h => ⟨(fromSpecStalk_specializes y q).mem_open U.isOpen hyU, h⟩⟩

/-- For a prime `𝔮` of `𝒪_{X,y}` with point `η`, the prime of `η` in `𝒪_{X,y}` is `𝔮`. -/
theorem comap_maximalIdeal_stalkSpecializes_fromSpecStalk (y : X)
    (q : PrimeSpectrum (X.presheaf.stalk y)) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk y q))).comap
      (X.presheaf.stalkSpecializes (fromSpecStalk_specializes y q)).hom = q.asIdeal := by
  ext a
  obtain ⟨U, hxU, -, r, rfl⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens X.presheaf y a
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_stalkSpecializes_germ_iff _ hxU r, fromSpecStalk_mem_basicOpen_iff hxU, not_not]

/-! ### Associated primes of a local ring and associated points -/

/-- If `𝔮` is an associated prime of the Noetherian local ring `𝒪_{Y,y}`, then the point of `Y`
given by `𝔮` is an associated point of `Y`. -/
theorem fromSpecStalk_mem_schemeAssociatedPoints {y : Y}
    [IsNoetherianRing (Y.presheaf.stalk y)] (q : PrimeSpectrum (Y.presheaf.stalk y))
    (hq : q.asIdeal ∈ associatedPrimes (Y.presheaf.stalk y) (Y.presheaf.stalk y)) :
    Y.fromSpecStalk y q ∈ Stacks.Divisors.schemeAssociatedPoints Y := by
  have hsp := fromSpecStalk_specializes y q
  let := (Y.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes hsp
  set P := (IsLocalRing.maximalIdeal (Y.presheaf.stalk (Y.fromSpecStalk y q))).comap
    (Y.presheaf.stalkSpecializes hsp).hom
  have hP : P = q.asIdeal := comap_maximalIdeal_stalkSpecializes_fromSpecStalk y q
  have hnoeth : IsNoetherianRing (Y.presheaf.stalk (Y.fromSpecStalk y q)) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hm : IsLocalRing.maximalIdeal (Y.presheaf.stalk (Y.fromSpecStalk y q)) ∈
      associatedPrimes (Y.presheaf.stalk (Y.fromSpecStalk y q))
        (Y.presheaf.stalk (Y.fromSpecStalk y q)) := by
    apply Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      P.primeCompl (Algebra.linearMap _ _)
    change P ∈ _
    rwa [hP]
  refine (isAssociatedPrimeStacks_iff_mem_associatedPrimes _).2 ?_
  rwa [LinearEquiv.AssociatedPrimes.eq (structureSheafStalkLinearEquiv Y (Y.fromSpecStalk y q))]

/-! ### Admissible representations of a local equation -/

/-- If `x' ⤳ x` and `x' ∉ Supp D`, then a local equation `g` of `D` at `x` can be written as
`d/c` with `c, d ∈ 𝒪_{X,x}` whose images in `𝒪_{X,x'}` are units. -/
theorem exists_mul_eq_isUnit_stalkSpecializes {D : X.CartierDivisor} {x' x : X} (h : x' ⤳ x)
    (hx' : x' ∉ cartierSupport D) {g : X.totalQuotientSheaf.presheaf.stalk x}
    (hg : IsLocalEquationAt D x g) {a₀ b₀ : X.presheaf.stalk x} (hab : IsFraction g a₀ b₀) :
    ∃ c d : X.presheaf.stalk x, stalkToTotalQuotient x c * g = stalkToTotalQuotient x d ∧
      IsUnit (X.presheaf.stalkSpecializes h c) ∧ IsUnit (X.presheaf.stalkSpecializes h d) := by
  obtain ⟨U, hxU, G, hG, rfl⟩ := hg
  have hx'U : x' ∈ U := h.mem_open U.isOpen hxU
  have hG' : IsLocalEquationAt D x' (X.totalQuotientSheaf.presheaf.germ U x' hx'U (G : _)) :=
    ⟨U, hx'U, G, hG, rfl⟩
  obtain ⟨w, hw⟩ := (isLocalEquationAt_one_of_notMem_cartierSupport hx').exists_eq_mul_units hG'
  rw [one_mul] at hw
  set sp := (X.presheaf.stalkSpecializes h).hom
  -- the specialization of `𝓜` is compatible with that of `𝒪`
  have hspM : ∀ r : X.presheaf.stalk x, X.totalQuotientSheaf.presheaf.stalkSpecializes h
      (stalkToTotalQuotient x r) = stalkToTotalQuotient x' (sp r) := fun r =>
    (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map_apply X.toTotalQuotientSheaf.hom h r).symm
  have hspG : X.totalQuotientSheaf.presheaf.stalkSpecializes h
      (X.totalQuotientSheaf.presheaf.germ U x hxU (G : _)) =
      X.totalQuotientSheaf.presheaf.germ U x' hx'U (G : _) := by
    rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have e1 : sp b₀ * w = sp a₀ := by
    apply stalkToTotalQuotient_injective x'
    have := congrArg (X.totalQuotientSheaf.presheaf.stalkSpecializes h) hab.2
    rw [map_mul, hspM, hspM, hspG, hw] at this
    rw [map_mul, this]
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes h
  set P := (IsLocalRing.maximalIdeal (X.presheaf.stalk x')).comap
    (X.presheaf.stalkSpecializes h).hom
  obtain ⟨⟨d, c⟩, hcd⟩ := IsLocalization.surj P.primeCompl (w : X.presheaf.stalk x')
  change (w : X.presheaf.stalk x') * sp c = sp d at hcd
  have hc : IsUnit (sp c) := IsLocalization.map_units (X.presheaf.stalk x') c
  have e2 : algebraMap (X.presheaf.stalk x) (X.presheaf.stalk x') (b₀ * d) =
      algebraMap (X.presheaf.stalk x) (X.presheaf.stalk x') (a₀ * c) := by
    change sp (b₀ * d) = sp (a₀ * c)
    rw [map_mul, map_mul, ← hcd, ← e1]
    ring
  obtain ⟨e, he⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) e2
  have hue : IsUnit (sp e) := IsLocalization.map_units (X.presheaf.stalk x') e
  refine ⟨e * c, e * d, ?_, ?_, ?_⟩
  · apply hab.1.mul_left_cancel
    have he' := congrArg (stalkToTotalQuotient x) he
    simp only [map_mul] at he' ⊢
    linear_combination (stalkToTotalQuotient x (e : X.presheaf.stalk x) *
      stalkToTotalQuotient x (c : X.presheaf.stalk x)) * hab.2 - he'
  · rw [map_mul]
    exact hue.mul hc
  · rw [map_mul, ← hcd]
    exact hue.mul (w.isUnit.mul hc)

/-- Under the pull-back condition, for each associated prime `𝔔` of `𝒪_{Y,y}` a local equation of
`D` at `f(y)` is a fraction `d/c` with `f^♯c, f^♯d ∉ 𝔔`. -/
theorem exists_mul_eq_notMem_of_mem_associatedPrimes {f : Y ⟶ X} {D : X.CartierDivisor}
    (hD : PullbackCondition f D) (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    {g : X.totalQuotientSheaf.presheaf.stalk (f y)} (hg : IsLocalEquationAt D (f y) g)
    {a₀ b₀ : X.presheaf.stalk (f y)} (hab : IsFraction g a₀ b₀)
    {Q : Ideal (Y.presheaf.stalk y)}
    (hQ : Q ∈ associatedPrimes (Y.presheaf.stalk y) (Y.presheaf.stalk y)) :
    ∃ c d : X.presheaf.stalk (f y),
      stalkToTotalQuotient (f y) c * g = stalkToTotalQuotient (f y) d ∧
      f.stalkMap y c ∉ Q ∧ f.stalkMap y d ∉ Q := by
  let q : PrimeSpectrum (Y.presheaf.stalk y) := ⟨Q, hQ.isPrime⟩
  have hsp := fromSpecStalk_specializes y q
  obtain ⟨c, d, hcd, hc, hd⟩ := exists_mul_eq_isUnit_stalkSpecializes
    (f.base.hom.map_specializes hsp) (hD _ (fromSpecStalk_mem_schemeAssociatedPoints q hQ)) hg hab
  have key : ∀ r, IsUnit (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hsp) r) →
      f.stalkMap y r ∉ Q := by
    intro r hr hmem
    have h1 : f.stalkMap y r ∈ (IsLocalRing.maximalIdeal _).comap
        (Y.presheaf.stalkSpecializes hsp).hom := by
      rwa [comap_maximalIdeal_stalkSpecializes_fromSpecStalk]
    rw [Ideal.mem_comap, ← Scheme.Hom.stalkSpecializes_stalkMap_apply] at h1
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 (hr.map _)
  exact ⟨c, d, hcd, key c hc, key d hd⟩

/-- In a Noetherian ring, an element lying in no associated prime is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_forall_notMem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] {t : R} (ht : ∀ P ∈ associatedPrimes R R, t ∉ P) :
    t ∈ nonZeroDivisors R := by
  by_contra hcon
  have : t ∈ ⋃ p ∈ associatedPrimes R R, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    exact hcon
  obtain ⟨Q, hQ, htQ⟩ := Set.mem_iUnion₂.1 this
  exact ht Q hQ htQ

/-- The ideal of denominators of `g ∈ 𝓜_{X,x}`: the `c ∈ 𝒪_{X,x}` with `c * g ∈ 𝒪_{X,x}`. -/
def denominatorIdeal {x : X} (g : X.totalQuotientSheaf.presheaf.stalk x) :
    Ideal (X.presheaf.stalk x) where
  carrier := {c | ∃ d, stalkToTotalQuotient x c * g = stalkToTotalQuotient x d}
  add_mem' := by
    rintro c₁ c₂ ⟨d₁, h₁⟩ ⟨d₂, h₂⟩
    exact ⟨d₁ + d₂, by rw [map_add, map_add, add_mul, h₁, h₂]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro r c ⟨d, h⟩
    exact ⟨r * d, by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, h]⟩

/-- Membership in `denominatorIdeal g`. -/
@[simp]
theorem mem_denominatorIdeal {x : X} {g : X.totalQuotientSheaf.presheaf.stalk x}
    {c : X.presheaf.stalk x} :
    c ∈ denominatorIdeal g ↔ ∃ d, stalkToTotalQuotient x c * g = stalkToTotalQuotient x d :=
  Iff.rfl

/-- **Prime avoidance.** If `X` and `Y` are locally Noetherian and no associated point of `Y`
maps into `Supp D`, every local equation `g` of `D` at `f(y)` is a fraction `a/b` with
`f^♯a, f^♯b` non-zero-divisors of `𝒪_{Y,y}`. -/
theorem exists_isFraction_stalkMap_mem_nonZeroDivisors [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] {f : Y ⟶ X} {D : X.CartierDivisor} (hD : PullbackCondition f D)
    (y : Y) {g : X.totalQuotientSheaf.presheaf.stalk (f y)} (hg : IsLocalEquationAt D (f y) g) :
    ∃ a b : X.presheaf.stalk (f y), IsFraction g a b ∧
      f.stalkMap y a ∈ nonZeroDivisors (Y.presheaf.stalk y) ∧
      f.stalkMap y b ∈ nonZeroDivisors (Y.presheaf.stalk y) := by
  classical
  set R := X.presheaf.stalk (f y)
  set S := Y.presheaf.stalk y
  set φ := (f.stalkMap y).hom
  obtain ⟨a₀, b₀, -, hb₀, hab₀⟩ := hg.exists_isFraction
  set J : Ideal R := denominatorIdeal g
  let s : Finset (Ideal R) := ((associatedPrimes.finite R R).union
    ((associatedPrimes.finite S S).image (Ideal.comap φ))).toFinset
  have hsR : ∀ P ∈ associatedPrimes R R, P ∈ s := fun P hP =>
    (Set.Finite.mem_toFinset _).2 (Or.inl hP)
  have hsS : ∀ Q ∈ associatedPrimes S S, Ideal.comap φ Q ∈ s := fun Q hQ =>
    (Set.Finite.mem_toFinset _).2 (Or.inr ⟨Q, hQ, rfl⟩)
  have hprime : ∀ P ∈ s, P.IsPrime := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    rcases hP with hP | ⟨Q, hQ, rfl⟩
    · exact hP.isPrime
    · have := hQ.isPrime
      exact Ideal.comap_isPrime φ Q
  have hnot : ∀ P ∈ s, ¬ J ≤ P := by
    intro P hP hJP
    rw [Set.Finite.mem_toFinset] at hP
    rcases hP with hP | ⟨Q, hQ, rfl⟩
    · have : b₀ ∈ (⋃ p ∈ associatedPrimes R R, (p : Set R)) :=
        Set.mem_biUnion hP (hJP ⟨a₀, hab₀.2⟩)
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors] at this
      exact this hb₀
    · obtain ⟨c, d, hcd, hc, -⟩ := exists_mul_eq_notMem_of_mem_associatedPrimes hD y hg hab₀ hQ
      exact hc (hJP ⟨d, hcd⟩)
  have hJ : ¬ ((J : Set R) ⊆ ⋃ P ∈ (↑s : Set (Ideal R)), ((fun P : Ideal R => P) P : Set R)) := by
    rw [Ideal.subset_union_prime (f := fun P : Ideal R => P) ⊤ ⊤ (fun P hP _ _ => hprime P hP)]
    exact fun ⟨P, hP, hJP⟩ => hnot P hP hJP
  obtain ⟨b, ⟨a, hba⟩, hb⟩ := Set.not_subset.1 hJ
  have hbP : ∀ P ∈ s, b ∉ P := fun P hP hbP => hb (Set.mem_biUnion (x := P) hP hbP)
  have hbR : b ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_forall_notMem_associatedPrimes fun P hP => hbP P (hsR P hP)
  have hbQ : ∀ Q ∈ associatedPrimes S S, φ b ∉ Q := fun Q hQ => hbP _ (hsS Q hQ)
  refine ⟨a, b, ⟨isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors hbR, hba⟩,
    mem_nonZeroDivisors_of_forall_notMem_associatedPrimes fun Q hQ haQ => ?_,
    mem_nonZeroDivisors_of_forall_notMem_associatedPrimes hbQ⟩
  obtain ⟨c, d, hcd, hc, hd⟩ := exists_mul_eq_notMem_of_mem_associatedPrimes hD y hg hab₀ hQ
  have e : a * c = b * d := by
    apply stalkToTotalQuotient_injective
    rw [map_mul, map_mul, ← hba, ← hcd]
    ring
  have hmem : φ b * φ d ∈ Q := by
    rw [← map_mul, ← e, map_mul]
    exact Q.mul_mem_right _ haQ
  exact (hQ.isPrime.mem_or_mem hmem).elim (hbQ Q hQ) hd

/-! ### Spreading admissible representations out -/

/-- A representation `g = a/b` of a local equation at `x` spreads out: `a`, `b` and `g` are germs
of sections `s_a, s_b, G` over an open `V₀ ∋ x`, `G` a local equation of `D` on `V₀`, and on a
smaller open `V ∋ x` the germs of `G` are the fractions of the germs of `s_a, s_b`. -/
theorem exists_fraction_nhds {D : X.CartierDivisor} {x : X}
    {g : X.totalQuotientSheaf.presheaf.stalk x} (hg : IsLocalEquationAt D x g)
    {a b : X.presheaf.stalk x} (hab : IsFraction g a b) :
    ∃ (V₀ : X.Opens) (hx₀ : x ∈ V₀) (G : (X.totalQuotientSheaf.obj.obj (op V₀))ˣ)
      (sa sb : Γ(X, V₀)), IsLocalEquationOn D V₀ G ∧ X.presheaf.germ V₀ x hx₀ sa = a ∧
      X.presheaf.germ V₀ x hx₀ sb = b ∧ ∃ (V : X.Opens) (hV : V ≤ V₀), x ∈ V ∧
        ∀ (p : X) (hp : p ∈ V),
          IsFraction (X.totalQuotientSheaf.presheaf.germ V₀ p (hV hp) (G : _))
            (X.presheaf.germ V₀ p (hV hp) sa) (X.presheaf.germ V₀ p (hV hp) sb) := by
  obtain ⟨U, hxU, G₀, hG₀, rfl⟩ := hg
  obtain ⟨Va, hxa, ta, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨Vb, hxb, tb, rfl⟩ := X.presheaf.exists_germ_eq b
  have hx₀ : x ∈ U ⊓ Va ⊓ Vb := ⟨⟨hxU, hxa⟩, hxb⟩
  have h1 : U ⊓ Va ⊓ Vb ≤ U := inf_le_left.trans inf_le_left
  have h2 : U ⊓ Va ⊓ Vb ≤ Va := inf_le_left.trans inf_le_right
  have h3 : U ⊓ Va ⊓ Vb ≤ Vb := inf_le_right
  have gsa : ∀ (p : X) (hp : p ∈ U ⊓ Va ⊓ Vb), X.presheaf.germ _ p hp
      (X.presheaf.map (homOfLE h2).op ta) = X.presheaf.germ Va p (h2 hp) ta :=
    fun p hp => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gsb : ∀ (p : X) (hp : p ∈ U ⊓ Va ⊓ Vb), X.presheaf.germ _ p hp
      (X.presheaf.map (homOfLE h3).op tb) = X.presheaf.germ Vb p (h3 hp) tb :=
    fun p hp => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gG : ∀ (p : X) (hp : p ∈ U ⊓ Va ⊓ Vb), X.totalQuotientSheaf.presheaf.germ _ p hp
      ((resUnits h1 G₀ : (X.totalQuotientSheaf.obj.obj (op (U ⊓ Va ⊓ Vb)))ˣ) : _) =
      X.totalQuotientSheaf.presheaf.germ U p (h1 hp) (G₀ : _) :=
    fun p hp => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  refine ⟨U ⊓ Va ⊓ Vb, hx₀, resUnits h1 G₀, X.presheaf.map (homOfLE h2).op ta,
    X.presheaf.map (homOfLE h3).op tb, hG₀.res h1, gsa x hx₀, gsb x hx₀, ?_⟩
  have hu : IsUnit (X.totalQuotientSheaf.presheaf.germ _ x hx₀
      (toTotalQuotient _ (X.presheaf.map (homOfLE h3).op tb))) := by
    rw [germ_toTotalQuotient, gsb]
    exact hab.1
  obtain ⟨W, hWV, hxW, hWu⟩ := exists_isUnit_map_of_isUnit_germ _ hx₀ _ hu
  have hrel : X.totalQuotientSheaf.presheaf.germ _ x hx₀
      (toTotalQuotient _ (X.presheaf.map (homOfLE h3).op tb) * (resUnits h1 G₀ : _)) =
      X.totalQuotientSheaf.presheaf.germ _ x hx₀
        (toTotalQuotient _ (X.presheaf.map (homOfLE h2).op ta)) := by
    rw [map_mul, germ_toTotalQuotient, germ_toTotalQuotient, gsa,
      gsb, gG]
    exact hab.2
  obtain ⟨W', hxW', i, j, hij⟩ := X.totalQuotientSheaf.presheaf.germ_eq x hx₀ hx₀ _ _ hrel
  refine ⟨W ⊓ W', inf_le_left.trans hWV, ⟨hxW, hxW'⟩, fun p hp => ⟨?_, ?_⟩⟩
  · have := hWu.map (X.totalQuotientSheaf.presheaf.germ W p hp.1).hom
    rwa [TopCat.Presheaf.germ_res_apply, germ_toTotalQuotient] at this
  · have := congrArg (X.totalQuotientSheaf.presheaf.germ W' p hp.2) hij
    rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, map_mul,
      germ_toTotalQuotient, germ_toTotalQuotient] at this

/-- If the pull-backs of the germs of `s_a, s_b ∈ Γ(V₀, 𝒪_X)` at `y` are units of `𝓜_{Y,y}`, then
on an open `W ∋ y` inside `f⁻¹(V)` there is a unit `G` of `Γ(W, 𝓜_Y)` whose germ at each `p ∈ W`
is `f^♯(s_a)_{f(p)} / f^♯(s_b)_{f(p)}`. -/
theorem exists_pullback_fraction_nhds (f : Y ⟶ X) {V₀ V : X.Opens} (hV : V ≤ V₀)
    (sa sb : Γ(X, V₀)) {y : Y} (hy : f y ∈ V)
    (ha : IsUnit (stalkToTotalQuotient y (f.stalkMap y (X.presheaf.germ V₀ (f y) (hV hy) sa))))
    (hb : IsUnit (stalkToTotalQuotient y (f.stalkMap y (X.presheaf.germ V₀ (f y) (hV hy) sb)))) :
    ∃ (W : Y.Opens) (hW : W ≤ f ⁻¹ᵁ V) (_ : y ∈ W) (G : (Y.totalQuotientSheaf.obj.obj (op W))ˣ),
      ∀ (p : Y) (hp : p ∈ W), IsFraction (Y.totalQuotientSheaf.presheaf.germ W p hp (G : _))
        (f.stalkMap p (X.presheaf.germ V₀ (f p) (hV (hW hp)) sa))
        (f.stalkMap p (X.presheaf.germ V₀ (f p) (hV (hW hp)) sb)) := by
  have hy₀ : y ∈ f ⁻¹ᵁ V₀ := hV hy
  have hua : IsUnit (Y.totalQuotientSheaf.presheaf.germ (f ⁻¹ᵁ V₀) y hy₀
      (toTotalQuotient _ (f.app V₀ sa))) := by
    rwa [germ_toTotalQuotient, ← Scheme.Hom.germ_stalkMap_apply f V₀ y hy₀]
  have hub : IsUnit (Y.totalQuotientSheaf.presheaf.germ (f ⁻¹ᵁ V₀) y hy₀
      (toTotalQuotient _ (f.app V₀ sb))) := by
    rwa [germ_toTotalQuotient, ← Scheme.Hom.germ_stalkMap_apply f V₀ y hy₀]
  obtain ⟨W₁, h₁, hy₁, hu₁⟩ := exists_isUnit_map_of_isUnit_germ _ hy₀ _ hua
  obtain ⟨W₂, h₂, hy₂, hu₂⟩ := exists_isUnit_map_of_isUnit_germ _ hy₀ _ hub
  have hWV : W₁ ⊓ W₂ ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V := inf_le_right
  have hW₀ : W₁ ⊓ W₂ ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V₀ := inf_le_left.trans (inf_le_left.trans h₁)
  have ua : IsUnit (Y.totalQuotientSheaf.presheaf.map (homOfLE hW₀).op
      (toTotalQuotient _ (f.app V₀ sa))) := by
    have := hu₁.map (Y.totalQuotientSheaf.presheaf.map
      (homOfLE (inf_le_left.trans inf_le_left : W₁ ⊓ W₂ ⊓ f ⁻¹ᵁ V ≤ W₁)).op).hom
    rwa [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
  have ub : IsUnit (Y.totalQuotientSheaf.presheaf.map (homOfLE hW₀).op
      (toTotalQuotient _ (f.app V₀ sb))) := by
    have := hu₂.map (Y.totalQuotientSheaf.presheaf.map
      (homOfLE (inf_le_left.trans inf_le_right : W₁ ⊓ W₂ ⊓ f ⁻¹ᵁ V ≤ W₂)).op).hom
    rwa [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
  refine ⟨W₁ ⊓ W₂ ⊓ f ⁻¹ᵁ V, hWV, ⟨⟨hy₁, hy₂⟩, hy⟩, ua.unit * ub.unit⁻¹, fun p hp => ?_⟩
  have gS : ∀ s : Γ(X, V₀), Y.totalQuotientSheaf.presheaf.germ _ p hp
      (Y.totalQuotientSheaf.presheaf.map (homOfLE hW₀).op (toTotalQuotient _ (f.app V₀ s))) =
      stalkToTotalQuotient p (f.stalkMap p (X.presheaf.germ V₀ (f p) (hW₀ hp) s)) := fun s => by
    rw [TopCat.Presheaf.germ_res_apply, germ_toTotalQuotient]
    exact congrArg _ (Scheme.Hom.germ_stalkMap_apply f V₀ p (hW₀ hp) s).symm
  refine ⟨?_, ?_⟩
  · rw [← gS]
    exact ub.map _
  · rw [← gS, ← gS, Units.val_mul, map_mul, IsUnit.unit_spec, mul_left_comm, ← map_mul,
      IsUnit.mul_val_inv, map_one, mul_one]

/-! ### Existence of the pull-back -/

/-- **Lazarsfeld §1.1.A, existence of pull-backs.** Let `f : Y ⟶ X` be a morphism of locally
Noetherian schemes and `D` a Cartier divisor on `X` such that no associated point of `Y` maps into
`Supp D`. Then `D` has a pull-back `f^*D` along `f`. -/
theorem exists_isPullback [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {f : Y ⟶ X}
    {D : X.CartierDivisor} (hD : PullbackCondition f D) : ∃ D', IsPullback f D D' := by
  have data : ∀ y : Y, ∃ (V₀ : X.Opens) (G₀ : (X.totalQuotientSheaf.obj.obj (op V₀))ˣ)
      (sa sb : Γ(X, V₀)) (W : Y.Opens) (hW : W ≤ f ⁻¹ᵁ V₀) (_ : y ∈ W)
      (G : (Y.totalQuotientSheaf.obj.obj (op W))ˣ),
      IsLocalEquationOn D V₀ G₀ ∧
      (∀ (p : Y) (hp : p ∈ W), IsFraction
        (X.totalQuotientSheaf.presheaf.germ V₀ (f p) (hW hp) (G₀ : _))
        (X.presheaf.germ V₀ (f p) (hW hp) sa) (X.presheaf.germ V₀ (f p) (hW hp) sb)) ∧
      (∀ (p : Y) (hp : p ∈ W), IsFraction (Y.totalQuotientSheaf.presheaf.germ W p hp (G : _))
        (f.stalkMap p (X.presheaf.germ V₀ (f p) (hW hp) sa))
        (f.stalkMap p (X.presheaf.germ V₀ (f p) (hW hp) sb))) ∧
      (∀ (hy : y ∈ W),
        f.stalkMap y (X.presheaf.germ V₀ (f y) (hW hy) sa) ∈ nonZeroDivisors _ ∧
        f.stalkMap y (X.presheaf.germ V₀ (f y) (hW hy) sb) ∈ nonZeroDivisors _) := by
    intro y
    obtain ⟨g, hg⟩ := exists_isLocalEquationAt D (f y)
    obtain ⟨a, b, hab, ha, hb⟩ := exists_isFraction_stalkMap_mem_nonZeroDivisors hD y hg
    obtain ⟨V₀, hx₀, G₀, sa, sb, hG₀, rfl, rfl, V, hV, hxV, hfrac⟩ := exists_fraction_nhds hg hab
    obtain ⟨W, hW, hyW, G, hG⟩ := exists_pullback_fraction_nhds f hV sa sb hxV
      (isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors ha)
      (isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors hb)
    exact ⟨V₀, G₀, sa, sb, W, fun p hp => hV (hW hp), hyW, G, hG₀,
      fun p hp => hfrac (f p) (hW hp), hG, fun _ => ⟨ha, hb⟩⟩
  choose V₀ G₀ sa sb W hW hyW G hG₀ hfracX hfracY hnzd using data
  have hcover : iSup W = ⊤ := top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ⟨y, hyW y⟩
  obtain ⟨D', hD'⟩ := exists_isLocalEquationOn_of_germ_eq_mul W hcover G
    (fun i j p hi hj => IsFraction.pullback_eq_mul (D := D)
      ⟨V₀ i, hW i hi, G₀ i, hG₀ i, rfl⟩ (hfracX i p hi)
      ⟨V₀ j, hW j hj, G₀ j, hG₀ j, rfl⟩ (hfracX j p hj) (hfracY i p hi) (hfracY j p hj))
  refine ⟨D', hD, fun y => ⟨_, _, ⟨_, ⟨V₀ y, hW y (hyW y), G₀ y, hG₀ y, rfl⟩,
    hfracX y y (hyW y)⟩, (hnzd y (hyW y)).1, (hnzd y (hyW y)).2, _,
    ⟨W y, hyW y, G y, hD' y, rfl⟩, hfracY y y (hyW y)⟩⟩

/-- **Lazarsfeld §1.1.A, the pull-back is well defined.** Let `f : Y ⟶ X` be a morphism of locally
Noetherian schemes and `D` a Cartier divisor on `X` such that no associated point of `Y` maps into
`Supp D`. Then there is exactly one pull-back `f^*D` of `D` along `f`; its local equations are
described by `MMP.Intersection.IsPullback.isLocalEquationAt`. -/
@[mmp "lem_p01a_divisor_pullback_well_defined"]
theorem existsUnique_isPullback [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {f : Y ⟶ X}
    {D : X.CartierDivisor} (hD : PullbackCondition f D) : ∃! D', IsPullback f D D' :=
  (exists_isPullback hD).imp fun _ hD' => ⟨hD', fun _ h => h.unique hD'⟩

attribute [mmp "lem_p01a_divisor_pullback_well_defined"] MMP.Intersection.IsPullback.unique
  MMP.Intersection.IsPullback.isLocalEquationAt

end MMP.Intersection
