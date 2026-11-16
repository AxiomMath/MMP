module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DltFloor.AdjointUniqueness
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentExistence
public import MMP.AlgebraicGeometry.Singularities.DltStrataSncLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.SeminormalLift
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.ProjectiveDivisorReduction

/-!
# The floor of a projective dlt pair is an sdlt adjoint pair

Let `(X, B)` be an effective rational `ℚ`-factorial projective dlt pair and `T = ⌊B⌋ ≠ 0` with
its reduced structure. The ideal of `T` is `𝒪_X(-T)`, and both it and `𝒪_X` are maximal
Cohen–Macaulay, so the depth lemma in `0 → 𝒪_X(-T) → 𝒪_X → 𝒪_T → 0` makes `T` Cohen–Macaulay.
The components `Tᵢ` of `T` are normal, and iterated dlt adjunction makes `T` a double normal
crossing in codimension one. Residue adjunction identifies the restriction of a local
generator of `𝒪_X(m(K_X + B))` with a local generator of the `m`-th adjoint sheaf of `T`.
Conversely every local generator of the adjoint sheaf is a unit multiple of such residues: the
ratio of two generators is a unit on each `Tᵢ`, its values agree across the double locus by the
residue identification, so it descends to `T` in codimension one by seminormality and extends
across codimension two since `T` is `S₂`.

## Main results

* `MMP.Fourfold.isCMScheme_and_exists_isSdltAdjointPair_of_isDltPair`

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Section 5.1
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.SdltFloor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

section Presentation

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  {T : Scheme.{0}} (ι : T ⟶ X)
  {hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
  (N : NormalizationComponents (ι ≫ sX) hfin)

/-- **A log residue presentation from a residue in a frame.** Let `ρ = ū s̄^{-m} (ds̄ ∧ dw̄)^{⊗m}`
be the residue along a floor component `Tₗ` of a form written in a frame at `y = ι(νₗ(η_Q))`,
where `s̄` is a local parameter of `Tₗ` along `Q`, `w̄` restrict functions `a` on `T`, and
`u = ε u₀` with `u₀` the restriction of a function `g` on `T`. Then `(V, a, g, ε)` presents the
residue of `ρ` along `Q`. -/
private theorem isLogResiduePresentation_of_eq {n' m : ℕ} (l : N.ι)
    (Q : MMP.Mori.PrimeDivisor (N.X l)) (V : T.Opens) (hV : (N.n l).base Q.genericPoint ∈ V)
    (a : Fin n' → Γ(T, V)) (g : Γ(T, V)) (ε : ℤ)
    (hsp : (N.n l ≫ ι) (genericPoint (N.X l)) ⤳ (N.n l ≫ ι) Q.genericPoint)
    (s u₀ : X.presheaf.stalk ((N.n l ≫ ι) Q.genericPoint))
    (w : Fin n' → X.presheaf.stalk ((N.n l ≫ ι) Q.genericPoint))
    (hs : IsUnit ((X.presheaf.stalkSpecializes hsp).hom s))
    (ρ : RationalPluriForms (N.n l ≫ ι ≫ sX) (n' + 1) m)
    (hρ : letI := functionFieldAlgebra (N.n l ≫ ι ≫ sX)
      ρ = ((N.n l ≫ ι).stalkMap (genericPoint (N.X l))).hom
          ((X.presheaf.stalkSpecializes hsp).hom ((ε : X.presheaf.stalk _) * u₀) *
          (((hs.unit⁻¹ : (X.presheaf.stalk ((N.n l ≫ ι) (genericPoint (N.X l))))ˣ) :
            X.presheaf.stalk ((N.n l ≫ ι) (genericPoint (N.X l)))) ^ m)) •
        PiTensorProduct.tprod (N.X l).functionField (fun _ : Fin m =>
          exteriorPower.ιMulti (N.X l).functionField (n' + 1) fun i =>
            KaehlerDifferential.D k (N.X l).functionField
              (((N.n l ≫ ι).stalkMap (genericPoint (N.X l))).hom
              ((X.presheaf.stalkSpecializes hsp).hom
                ((Fin.cons s w : Fin (n' + 1) → X.presheaf.stalk _) i)))))
    (hz : (N.X l).ord (((N.n l ≫ ι).stalkMap (genericPoint (N.X l))).hom
      ((X.presheaf.stalkSpecializes hsp).hom s)) Q.genericPoint = 1)
    (ha : ∀ i, (N.X l).presheaf.germ ((N.n l) ⁻¹ᵁ V) Q.genericPoint hV ((N.n l).app V (a i)) =
      ((N.n l ≫ ι).stalkMap Q.genericPoint).hom (w i))
    (hg : (N.X l).presheaf.germ ((N.n l) ⁻¹ᵁ V) Q.genericPoint hV ((N.n l).app V g) =
      ((N.n l ≫ ι).stalkMap Q.genericPoint).hom u₀)
    (hw : letI : Algebra k ((N.X l).residueField Q.genericPoint) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (N.n l ≫ ι ≫ sX).appTop ≫
          (N.X l).Γevaluation Q.genericPoint).hom.toAlgebra
      LinearIndependent ((N.X l).residueField Q.genericPoint) fun i =>
        KaehlerDifferential.D k ((N.X l).residueField Q.genericPoint)
          ((N.X l).residue Q.genericPoint (((N.n l ≫ ι).stalkMap Q.genericPoint).hom (w i)))) :
    IsLogResiduePresentation N (n' + 1) m l Q V hV a g ε ρ := by
  classical
  letI := functionFieldAlgebra (N.n l ≫ ι ≫ sX)
  set φQ := ((N.n l ≫ ι).stalkMap Q.genericPoint).hom
  set φg := ((N.n l ≫ ι).stalkMap (genericPoint (N.X l))).hom
  set sp := (X.presheaf.stalkSpecializes hsp).hom
  have hco : ∀ v, algebraMap ((N.X l).presheaf.stalk Q.genericPoint) (N.X l).functionField
      (φQ v) = φg (sp v) := fun v =>
    (Scheme.Hom.stalkSpecializes_stalkMap_apply (N.n l ≫ ι) _ _
      (genericPoint_specializes Q.genericPoint) v).symm
  set z := φg (sp s) with hzdef
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, Scheme.ord_zero] at hz; exact zero_ne_one hz
  have hinv : φg ((hs.unit⁻¹ : (X.presheaf.stalk _)ˣ) : X.presheaf.stalk _) = z⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [hzdef, ← map_mul]
    have : ((hs.unit⁻¹ : (X.presheaf.stalk _)ˣ) : X.presheaf.stalk
        ((N.n l ≫ ι) (genericPoint (N.X l)))) * sp s = 1 := hs.unit.inv_mul
    rw [this, map_one]
  refine ⟨z, φQ ((ε : X.presheaf.stalk _) * u₀), hz, ?_, ?_, ?_⟩
  · beta_reduce
    have hF : (fun j : Fin (n' + 1) => if hj : j.val = 0 then
          z⁻¹ • KaehlerDifferential.D k (N.X l).functionField z
        else KaehlerDifferential.D k (N.X l).functionField
          (algebraMap _ (N.X l).functionField ((N.X l).presheaf.germ ((N.n l) ⁻¹ᵁ V)
            Q.genericPoint (show Q.genericPoint ∈ (N.n l) ⁻¹ᵁ V from hV)
            ((N.n l).app V (a ⟨j.val - 1, by omega⟩))))) =
        Function.update (fun i => KaehlerDifferential.D k (N.X l).functionField
          (φg (sp ((Fin.cons s w : Fin (n' + 1) → X.presheaf.stalk _) i)))) 0
          (z⁻¹ • KaehlerDifferential.D k (N.X l).functionField z) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [dif_pos (show ((0 : Fin (n' + 1)) : ℕ) = 0 from rfl), Function.update_self]
      · rw [dif_neg (by simp), Function.update_of_ne (Fin.succ_ne_zero i), Fin.cons_succ]
        have hi : (⟨(Fin.succ i).val - 1, by have := i.isLt; simp⟩ : Fin n') = i :=
          Fin.ext (by simp)
        rw [hi, ha, hco]
    have hupd : Function.update (fun i => KaehlerDifferential.D k (N.X l).functionField
        (φg (sp ((Fin.cons s w : Fin (n' + 1) → X.presheaf.stalk _) i)))) 0
        (KaehlerDifferential.D k (N.X l).functionField z) =
        fun i => KaehlerDifferential.D k (N.X l).functionField
          (φg (sp ((Fin.cons s w : Fin (n' + 1) → X.presheaf.stalk _) i))) :=
      Function.update_eq_self_iff.mpr rfl
    have hsc : φg (sp ((ε : X.presheaf.stalk _) * u₀) *
        (((hs.unit⁻¹ : (X.presheaf.stalk ((N.n l ≫ ι) (genericPoint (N.X l))))ˣ) :
          X.presheaf.stalk ((N.n l ≫ ι) (genericPoint (N.X l)))) ^ m)) =
        algebraMap _ (N.X l).functionField (φQ ((ε : X.presheaf.stalk _) * u₀)) * z⁻¹ ^ m := by
      rw [map_mul, map_pow, hinv, hco]
    rw [hsc] at hρ
    rw [hF, AlternatingMap.map_update_smul, hupd, hρ, mul_smul]
    congr 1
    exact (MMP.Mori.tprod_const_smul _ _).symm
  · letI : Algebra k ((N.X l).residueField Q.genericPoint) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (N.n l ≫ ι ≫ sX).appTop ≫
        (N.X l).Γevaluation Q.genericPoint).hom.toAlgebra
    beta_reduce
    simp only [ha]
    exact Stacks.EtaleCohomology.ιMulti_ne_zero_of_linearIndependent hw
  · beta_reduce
    rw [map_mul, map_mul, map_intCast, map_intCast, hg]

end Presentation

section Floor

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {B : QDivisor X}
  {T : Scheme.{0}} (ι : T ⟶ X) [IsClosedImmersion ι] [IsReduced T]

/-- The stalk of the unit presheaf of modules is the stalk of the presheaf of rings, as a module
over itself. -/
private noncomputable def unitStalkLinearEquiv {X : TopCat.{0}}
    (R : TopCat.Presheaf CommRingCat.{0} X) (x : X) :
    (ToType (TopCat.Presheaf.stalk
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).presheaf x))
      ≃ₗ[ToType (R.stalk x)] (ToType (R.stalk x)) := by
  set pIso : (forget₂ CommRingCat.{0} RingCat.{0} ⋙
      forget₂ RingCat.{0} AddCommGrpCat.{0}).obj (R.stalk x) ≅
      TopCat.Presheaf.stalk
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).presheaf x :=
    preservesColimitIso (forget₂ CommRingCat.{0} RingCat.{0} ⋙
      forget₂ RingCat.{0} AddCommGrpCat.{0}) ((OpenNhds.inclusion x).op ⋙ R) with hpIso
  set addE : (ToType (TopCat.Presheaf.stalk
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).presheaf x)) ≃+
      ToType (R.stalk x) := pIso.symm.addCommGroupIsoToAddEquiv
  have key : ∀ (U : Opens X) (hxU : x ∈ U)
      (s : ToType ((PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).obj
        (Opposite.op U))),
      addE ((ConcreteCategory.hom (TopCat.Presheaf.germ
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).presheaf U x hxU)) s) =
      (ConcreteCategory.hom (R.germ U x hxU)) s := by
    intro U hxU s
    have h := ι_preservesColimitIso_inv (forget₂ CommRingCat.{0} RingCat.{0} ⋙
      forget₂ RingCat.{0} AddCommGrpCat.{0}) ((OpenNhds.inclusion x).op ⋙ R)
      (Opposite.op ⟨U, hxU⟩)
    rw [← hpIso] at h
    have h2 := congrArg (fun (f : _ ⟶ _) => (ConcreteCategory.hom f) s) h
    change (ConcreteCategory.hom (Limits.colimit.ι (((OpenNhds.inclusion x).op ⋙ R) ⋙
          (forget₂ CommRingCat.{0} RingCat.{0} ⋙ forget₂ RingCat.{0} AddCommGrpCat.{0}))
          (Opposite.op ⟨U, hxU⟩) ≫ pIso.inv)) s =
        (ConcreteCategory.hom ((forget₂ CommRingCat.{0} RingCat.{0} ⋙
          forget₂ RingCat.{0} AddCommGrpCat.{0}).map
          (Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ R) (Opposite.op ⟨U, hxU⟩)))) s
    exact h2
  refine { addE with toFun := addE, map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).presheaf m
  obtain ⟨V, hxV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
  set W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hr : (ConcreteCategory.hom (R.germ V x hxV)) r₀ =
      (ConcreteCategory.hom (R.germ W x hxW))
        ((ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  have hm : (ConcreteCategory.hom (TopCat.Presheaf.germ
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).presheaf U x hxU)) m₀ =
      (ConcreteCategory.hom (TopCat.Presheaf.germ
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).presheaf W x hxW))
        ((ConcreteCategory.hom ((PresheafOfModules.unit
          (R ⋙ forget₂ _ RingCat.{0})).presheaf.map (homOfLE (inf_le_left)).op)) m₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  rw [hr, hm]
  set rr : ToType (R.obj (Opposite.op W)) :=
    (ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀
  set mm : ToType ((PresheafOfModules.unit
      (R ⋙ forget₂ _ RingCat.{0})).obj (Opposite.op W)) :=
    (ConcreteCategory.hom ((PresheafOfModules.unit
      (R ⋙ forget₂ _ RingCat.{0})).presheaf.map (homOfLE (inf_le_left)).op)) m₀
  rw [← PresheafOfModules.germ_smul
    (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})) x W hxW rr mm]
  rw [key, key]
  change ↑(R.obj (Opposite.op W)) at mm
  change (R.germ W x hxW).hom (rr * mm) =
    (R.germ W x hxW).hom rr * (R.germ W x hxW).hom mm
  exact map_mul _ _ _

/-- `unitStalkLinearEquiv` sends the germ of a section of the unit presheaf to its germ in the
stalk of the presheaf of rings. -/
private theorem unitStalkLinearEquiv_germ {X : TopCat.{0}}
    (R : TopCat.Presheaf CommRingCat.{0} X) {U : Opens X} {x : X} (hxU : x ∈ U)
    (s : ToType ((PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).obj (Opposite.op U))) :
    unitStalkLinearEquiv R x ((ConcreteCategory.hom (TopCat.Presheaf.germ
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{0})).presheaf U x hxU)) s) =
      (ConcreteCategory.hom (R.germ U x hxU)) s := by
  have h := ι_preservesColimitIso_inv (forget₂ CommRingCat.{0} RingCat.{0} ⋙
    forget₂ RingCat.{0} AddCommGrpCat.{0}) ((OpenNhds.inclusion x).op ⋙ R)
    (Opposite.op ⟨U, hxU⟩)
  have h2 := congrArg (fun (f : _ ⟶ _) => (ConcreteCategory.hom f) s) h
  exact h2

/-- A Cohen–Macaulay scheme satisfies Serre's condition `S₂`. -/
private theorem satisfiesS2_of_isCMScheme {T : Scheme.{0}} (h : IsCMScheme T) : SatisfiesS2 T := by
  intro x
  have hx : IsCMModule (T.presheaf.stalk x) (T.presheaf.stalk x) :=
    isCMModule_of_linearEquiv (unitStalkLinearEquiv T.presheaf x) (h x)
  rcases hx with hsub | ⟨xs, ⟨hm, hreg⟩, hlen⟩
  · exact absurd hsub (not_subsingleton _)
  · refine ⟨xs, hm,
      (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hreg, ?_⟩
    rw [← Module.supportDim_self_eq_ringKrullDim, ← hlen]
    exact min_le_right _ _

/-- The stalk at `x` of a morphism of `𝒪_X`-modules, as an `𝒪_{X,x}`-linear map. -/
private noncomputable def stalkLinearMap {X : Scheme.{0}} {M N : X.Modules} (f : M ⟶ N) (x : X) :
    ToType (TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[X.presheaf.stalk x]
      ToType (TopCat.Presheaf.stalk N.val.presheaf x) where
  toFun := (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map f
  map_add' := map_add _
  map_smul' := by
    intro r m
    obtain ⟨U, hxU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    obtain ⟨V, hxV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
    set W : Opens X := U ⊓ V
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right : W ⟶ V) x hxW,
      ← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE inf_le_left : W ⟶ U) x hxW]
    set rr := (X.presheaf.map (homOfLE inf_le_right : W ⟶ V).op).hom r₀
    set mm := (M.val.presheaf.map (homOfLE inf_le_left : W ⟶ U).op).hom m₀
    have e1 := PresheafOfModules.germ_smul M.val x W hxW rr mm
    erw [← e1]
    simp only [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply]
    erw [← PresheafOfModules.germ_smul N.val x W hxW rr]
    congr 1
    exact (f.val.app _).hom.map_smul rr mm

/-- `stalkLinearMap` sends a germ to the germ of the image section. -/
private theorem stalkLinearMap_germ {X : Scheme.{0}} {M N : X.Modules} (f : M ⟶ N) {x : X}
    {W : X.Opens} (hx : x ∈ W) (s : ToType (M.val.presheaf.obj (Opposite.op W))) :
    stalkLinearMap f x ((ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf W x hx)) s) =
      (ConcreteCategory.hom (TopCat.Presheaf.germ N.val.presheaf W x hx)) (f.app W s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx _ s

/-- The stalk at `x` of an isomorphism of `𝒪_X`-modules, as an `𝒪_{X,x}`-linear equivalence. -/
private noncomputable def stalkLinearEquiv {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N)
    (x : X) :
    ToType (TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[X.presheaf.stalk x]
      ToType (TopCat.Presheaf.stalk N.val.presheaf x) :=
  { stalkLinearMap e.hom x with
    invFun := stalkLinearMap e.inv x
    left_inv := fun m => ConcreteCategory.congr_hom
      ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).mapIso
        e).hom_inv_id m
    right_inv := fun m => ConcreteCategory.congr_hom
      ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).mapIso
        e).inv_hom_id m }

/-- The germ at the generic point of its component of a regular function, read through
`𝒪_{X,E}`. -/
private theorem germ_componentGenericPoint_eq_toComponent {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X)
    {W : X.Opens} (hE : E.genericPoint ∈ W) (r : Γ(X, W)) :
    (X.presheaf.germ W (componentGenericPoint X E.component)
      (E.specializes_genericPoint.mem_open W.isOpen hE)).hom r =
      E.toComponent.hom ((X.presheaf.germ W E.genericPoint hE).hom r) :=
  (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hE E.specializes_genericPoint r).symm

/-- A regular function has nonnegative order along every prime divisor. -/
private theorem ordGE_zero_germ {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    (E : MMP.Mori.PrimeDivisor X) {W : X.Opens}
    (hE : E.genericPoint ∈ W) (r : Γ(X, W)) :
    E.OrdGE 0 ((X.presheaf.germ W (componentGenericPoint X E.component)
      (E.specializes_genericPoint.mem_open W.isOpen hE)).hom r) := by
  rw [germ_componentGenericPoint_eq_toComponent E hE]
  by_cases h : (X.presheaf.germ W E.genericPoint hE).hom r = 0
  · rw [h, map_zero]; exact Or.inl rfl
  · exact Or.inr (by rw [WithZero.exp_zero]; exact E.one_le_valuation_toComponent h)

/-- A regular function has positive order along a prime divisor exactly when it vanishes at its
generic point. -/
private theorem ordGE_one_germ_iff {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    (E : MMP.Mori.PrimeDivisor X) {W : X.Opens}
    (hE : E.genericPoint ∈ W) (r : Γ(X, W)) :
    E.OrdGE 1 ((X.presheaf.germ W (componentGenericPoint X E.component)
      (E.specializes_genericPoint.mem_open W.isOpen hE)).hom r) ↔
      E.genericPoint ∉ X.basicOpen r := by
  rw [germ_componentGenericPoint_eq_toComponent E hE, Scheme.mem_basicOpen _ _ _ hE]
  refine ⟨fun h hu => ?_, fun hu => E.ordGE_one_toComponent
    ((IsLocalRing.mem_maximalIdeal _).mpr hu)⟩
  rcases h with h0 | hv
  · exact hu.ne_zero (stalkToRationalFunctions_injective (X := X) E.genericPoint_mem_component
      (h0.trans (map_zero _).symm))
  · rw [E.valuation_toComponent_of_isUnit hu, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv
    exact absurd hv (by norm_num)

/-- A prime divisor in the support of `⌊B⌋` is in the support of `B`, for a boundary `B` with
coefficients in `[0, 1]`. -/
private theorem mem_support_of_mem_roundDown_support {X : Scheme.{0}} {B : QDivisor X}
    (h0 : ∀ P, 0 ≤ B.coeff P) (h1 : ∀ P, B.coeff P ≤ 1) {G : MMP.Mori.PrimeDivisor X}
    (hG : G ∈ B.roundDown.support) : G ∈ B.support := by
  rw [Finsupp.mem_support_iff]
  change B.coeff G ≠ 0
  rw [coeff_eq_one_of_mem_roundDown_support h0 h1 hG]
  exact one_ne_zero

/-- A regular function on `W` is a section of `𝒪_X(-⌊B⌋)` exactly when it vanishes on the reduced
floor `T`, for a boundary `B` with coefficients in `[0, 1]`. -/
private theorem isDivisorialSection_neg_roundDown_iff {X T : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (ι : T ⟶ X) {B : QDivisor X} (h0 : ∀ P, 0 ≤ B.coeff P)
    (h1 : ∀ P, B.coeff P ≤ 1)
    (hT : Set.range ι.base = ⋃ P ∈ B.roundDown.support, (P.support : Set X)) {W : X.Opens}
    (r : Γ(X, W)) :
    (-B.roundDown).IsDivisorialSection W ((toRationalFunctionsPresheaf X).app (Opposite.op W) r) ↔
      ∀ y : T, ι.base y ∈ W → ι.base y ∉ X.basicOpen r := by
  have hcoeff : ∀ P, -(-B.roundDown).coeff P = B.roundDown.coeff P := fun P => by
    rw [DivisorWithCoeffs.coeff_neg, neg_neg]
  constructor
  · intro h y hyW hyr
    have hy : ι.base y ∈ Set.range ι.base := ⟨y, rfl⟩
    rw [hT] at hy
    obtain ⟨_, ⟨P, rfl⟩, hy⟩ := hy
    obtain ⟨hP, hyP⟩ := Set.mem_iUnion.mp hy
    have hPW : (P.support ∩ W : Set X).Nonempty := ⟨_, hyP, hyW⟩
    have hηW := P.genericPoint_mem_of_nonempty hPW
    have hP1 : B.roundDown.coeff P = 1 := by
      rw [DivisorWithCoeffs.coeff_roundDown, coeff_eq_one_of_mem_roundDown_support h0 h1 hP]
      simp
    have := h P hPW
    rw [hcoeff, hP1] at this
    have hη := (ordGE_one_germ_iff P hηW r).mp this
    apply hη
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyP
    exact (specializes_iff_mem_closure.mpr hyP).mem_open (X.basicOpen r).isOpen hyr
  · intro h E hE
    have hηW := E.genericPoint_mem_of_nonempty hE
    rw [hcoeff]
    by_cases hEs : E ∈ B.roundDown.support
    · have hE1 : B.roundDown.coeff E = 1 := by
        rw [DivisorWithCoeffs.coeff_roundDown, coeff_eq_one_of_mem_roundDown_support h0 h1 hEs]
        simp
      rw [hE1]
      refine (ordGE_one_germ_iff E hηW r).mpr ?_
      have : E.genericPoint ∈ Set.range ι.base := by
        rw [hT]
        refine Set.mem_biUnion hEs ?_
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      obtain ⟨y, hy⟩ := this
      rw [← hy] at hηW ⊢
      exact h y hηW
    · rw [show B.roundDown.coeff E = 0 from Finsupp.notMem_support_iff.mp hEs]
      exact ordGE_zero_germ E hηW r

/-- **The ideal of the floor is `𝒪_X(-⌊B⌋)`.** For a boundary `B` with coefficients in `[0, 1]`
and the reduced closed subscheme `T` with support `⌊B⌋`, the stalk at `ι t` of `𝒪_X(-⌊B⌋)` is,
as an `𝒪_{X,ι t}`-module, the kernel of `𝒪_{X,ι t} → 𝒪_{T,t}`: a function vanishes on `T` near
`ι t` exactly when its order along every component of `⌊B⌋` through `ι t` is positive. -/
private theorem nonempty_stalk_divisorialSheaf_roundDown_linearEquiv_ker {X T : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (ι : T ⟶ X) [IsClosedImmersion ι]
    [IsReduced T] {B : QDivisor X} (h0 : ∀ P, 0 ≤ B.coeff P) (h1 : ∀ P, B.coeff P ≤ 1)
    (hT : Set.range ι.base = ⋃ P ∈ B.roundDown.support, (P.support : Set X)) (t : T) :
    Nonempty (ToType (TopCat.Presheaf.stalk (-B.roundDown).divisorialSheaf.val.presheaf
      (ι.base t)) ≃ₗ[X.presheaf.stalk (ι.base t)] RingHom.ker (ι.stalkMap t).hom) := by
  classical
  set x := ι.base t with hxdef
  have hD0 : -B.roundDown ≤ 0 := fun P => by
    change (-B.roundDown).coeff P ≤ (0 : Divisor X).coeff P
    rw [DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_zero,
      DivisorWithCoeffs.coeff_roundDown, neg_nonpos]
    exact Int.floor_nonneg.mpr (h0 P)
  let φ₀ := Divisor.structureSheafToDivisorialSheaf (le_refl (0 : Divisor X))
  let Ψ : ToType (TopCat.Presheaf.stalk (-B.roundDown).divisorialSheaf.val.presheaf x)
      →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    (unitStalkLinearEquiv X.presheaf x).toLinearMap ∘ₗ
      (stalkLinearMap Divisor.divisorialSheafZeroIso.hom x) ∘ₗ
        stalkLinearMap (Divisor.divisorialSheafInclusion hD0) x
  -- `Ψ` on germs
  have hΨ : ∀ (W : X.Opens) (hxW : x ∈ W)
      (s : ToType ((-B.roundDown).divisorialSheaf.val.obj (Opposite.op W))) (r : Γ(X, W)),
      (toRationalFunctionsPresheaf X).app (Opposite.op W) r =
        (s : (-B.roundDown).divisorialSubmodule W).1 →
      Ψ ((ConcreteCategory.hom (TopCat.Presheaf.germ
        (-B.roundDown).divisorialSheaf.val.presheaf W x hxW)) s) =
        (ConcreteCategory.hom (X.presheaf.germ W x hxW)) r := by
    intro W hxW s r hr
    have h1 : (Divisor.divisorialSheafInclusion hD0).app W s = φ₀.app W r :=
      Subtype.ext ((Divisor.coe_divisorialSheafInclusion_app hD0 W s).trans
        (hr.symm.trans (Divisor.coe_structureSheafToDivisorialSheaf_app _ W r).symm))
    have h2 : Divisor.divisorialSheafZeroIso.hom.app W (φ₀.app W r) = r := by
      change (φ₀.app W ≫ (inv φ₀).app W) r = r
      rw [← Scheme.Modules.Hom.comp_app, IsIso.hom_inv_id]
      rfl
    change unitStalkLinearEquiv X.presheaf x (stalkLinearMap Divisor.divisorialSheafZeroIso.hom x
      (stalkLinearMap (Divisor.divisorialSheafInclusion hD0) x _)) = _
    rw [stalkLinearMap_germ (Divisor.divisorialSheafInclusion hD0) hxW s, h1]
    refine (congrArg (unitStalkLinearEquiv X.presheaf x)
      (stalkLinearMap_germ Divisor.divisorialSheafZeroIso.hom hxW (φ₀.app W r))).trans ?_
    rw [h2]
    exact unitStalkLinearEquiv_germ X.presheaf hxW r
  -- every section of `𝒪_X(-⌊B⌋)` is a regular function
  have hreg : ∀ (W : X.Opens)
      (s : ToType ((-B.roundDown).divisorialSheaf.val.obj (Opposite.op W))),
      ∃ r : Γ(X, W), (toRationalFunctionsPresheaf X).app (Opposite.op W) r =
        (s : (-B.roundDown).divisorialSubmodule W).1 :=
    fun W s => Divisor.IsDivisorialSection.exists_eq
      ((s : (-B.roundDown).divisorialSubmodule W).2.mono hD0)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ m
    obtain ⟨r, hr⟩ := hreg W s
    rw [hΨ W hxW s r hr, ← map_zero (ConcreteCategory.hom (X.presheaf.germ W x hxW))] at hm
    obtain ⟨W', hxW', i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq X.presheaf x hxW hxW r 0 hm
    have hi : i₂ = i₁ := Subsingleton.elim _ _
    subst hi
    have h0s : (ConcreteCategory.hom ((-B.roundDown).divisorialSheaf.val.presheaf.map i₂.op)) s =
        0 := by
      apply Subtype.ext
      change (rationalFunctionsPresheaf X).map i₂.op
        (s : (-B.roundDown).divisorialSubmodule W).1 = 0
      rw [← hr, ← toRationalFunctionsPresheaf_app_map, heq, map_zero, map_zero]
    rw [← TopCat.Presheaf.germ_res_apply _ i₂ x hxW', h0s, map_zero]
  have hrange : LinearMap.range Ψ = RingHom.ker (ι.stalkMap t).hom := by
    ext a
    constructor
    · rintro ⟨m, rfl⟩
      obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ m
      obtain ⟨r, hr⟩ := hreg W s
      rw [hΨ W hxW s r hr]
      have hs := (s : (-B.roundDown).divisorialSubmodule W).2
      rw [← hr] at hs
      have hv := (isDivisorialSection_neg_roundDown_iff ι h0 h1 hT r).mp hs
      rw [RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply]
      have hz : (ConcreteCategory.hom (ι.app W)) r = 0 := by
        apply eq_zero_of_basicOpen_eq_bot
        rw [← Scheme.Hom.preimage_basicOpen]
        exact eq_bot_iff.mpr fun y hy => hv y (X.basicOpen_le r hy) hy
      rw [hz, map_zero]
    · intro ha
      obtain ⟨W, hxW, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
      have ha' := RingHom.mem_ker.mp ha
      rw [Scheme.Hom.germ_stalkMap_apply,
        ← map_zero (ConcreteCategory.hom (T.presheaf.germ (ι ⁻¹ᵁ W) t hxW))] at ha'
      obtain ⟨V, htV, iV, iV', hV⟩ := TopCat.Presheaf.germ_eq T.presheaf t hxW hxW _ 0 ha'
      rw [map_zero] at hV
      obtain ⟨W₁, hW₁, hW₁V⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
      let W₂ : X.Opens := W ⊓ ⟨W₁, hW₁⟩
      have hxW₂ : x ∈ W₂ := ⟨hxW, show t ∈ ι.base ⁻¹' W₁ by rw [hW₁V]; exact htV⟩
      let r₂ := (ConcreteCategory.hom (X.presheaf.map (homOfLE inf_le_left : W₂ ⟶ W).op)) r
      have hle : ι ⁻¹ᵁ W₂ ≤ V := fun z hz => by
        have : z ∈ ι.base ⁻¹' W₁ := hz.2
        rwa [hW₁V] at this
      have hz : (ConcreteCategory.hom (ι.app W₂)) r₂ = 0 := by
        change (ConcreteCategory.hom (X.presheaf.map (homOfLE inf_le_left : W₂ ⟶ W).op ≫
          ι.app W₂)) r = 0
        rw [Scheme.Hom.naturality, ConcreteCategory.comp_apply]
        have : ((Opens.map ι.base).map (homOfLE inf_le_left : W₂ ⟶ W).op.unop).op =
            iV.op ≫ (homOfLE hle).op :=
          congrArg Quiver.Hom.op (Subsingleton.elim _ _)
        rw [this, Functor.map_comp, ConcreteCategory.comp_apply, hV, map_zero]
      have hv : ∀ y : T, ι.base y ∈ W₂ → ι.base y ∉ X.basicOpen r₂ := by
        intro y _ hyr
        have : y ∈ ι ⁻¹ᵁ X.basicOpen r₂ := hyr
        rwa [Scheme.Hom.preimage_basicOpen, hz, Scheme.basicOpen_zero] at this
      let s₂ : ToType ((-B.roundDown).divisorialSheaf.val.obj (Opposite.op W₂)) :=
        (⟨(toRationalFunctionsPresheaf X).app (Opposite.op W₂) r₂,
          (isDivisorialSection_neg_roundDown_iff ι h0 h1 hT r₂).mpr hv⟩ :
          (-B.roundDown).divisorialSubmodule W₂)
      refine ⟨(ConcreteCategory.hom (TopCat.Presheaf.germ
        (-B.roundDown).divisorialSheaf.val.presheaf W₂ x hxW₂)) s₂, ?_⟩
      rw [hΨ W₂ hxW₂ s₂ r₂ rfl]
      exact TopCat.Presheaf.germ_res_apply X.presheaf _ x hxW₂ r
  exact ⟨(LinearEquiv.ofInjective Ψ hinj).trans (LinearEquiv.ofEq _ _ hrange)⟩

/-- If the image of `ι` misses the generic point of the integral scheme `X`, then the kernel of
`𝒪_{X,ι t} → 𝒪_{T,t}` is nonzero for every `t`. -/
private theorem ker_stalkMap_ne_bot {X T : Scheme.{0}} [IsIntegral X] (ι : T ⟶ X)
    [IsClosedImmersion ι] [IsReduced T] (hι : genericPoint X ∉ Set.range ι.base) (t : T) :
    RingHom.ker (ι.stalkMap t).hom ≠ ⊥ := by
  obtain ⟨_, ⟨U, hU', rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ι.base t)) isOpen_univ
  -- the open complement of `T`
  let V : X.Opens := ⟨(Set.range ι.base)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hξU : genericPoint X ∈ U :=
    ((genericPoint_spec X).specializes (Set.mem_univ (ι.base t))).mem_open U.isOpen hxU
  obtain ⟨f, hfV, hξf⟩ :=
    (show IsAffineOpen U from hU').exists_basicOpen_le (V := V) ⟨genericPoint X, hι⟩ hξU
  intro hbot
  have hf0 : f ≠ 0 := by
    rintro rfl
    rwa [Scheme.basicOpen_zero] at hξf
  apply hf0
  apply germ_injective_of_isIntegral X (ι.base t) hxU
  rw [map_zero]
  have : (ι.stalkMap t).hom ((X.presheaf.germ _ (ι.base t) hxU).hom f) = 0 := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    have hz : (ι.app _).hom f = 0 := by
      apply eq_zero_of_basicOpen_eq_bot
      rw [← Scheme.Hom.preimage_basicOpen]
      exact eq_bot_iff.mpr fun y hy => hfV hy ⟨y, rfl⟩
    rw [hz, map_zero]
  have := RingHom.mem_ker.mpr this
  rwa [hbot] at this

/-- The residue identification along the floor: for a Cartier multiple `m(K_X + B)`, the Poincaré
residues along the floor components of a local generator of `𝒪_X(m(K_X + B))` exist and form a
local generator of the `m`-th adjoint sheaf of `T`. -/
private def ResidueIdentification
    {hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents (ι ≫ sX) hfin) (n : ℕ) (K : Divisor X) (B : QDivisor X)
    (Θ : ∀ i, QDivisor (N.X i)) : Prop :=
  ∀ m : ℕ, 0 < m → ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor →
    ∀ (W : X.Opens) (τ : RationalPluriForms sX (n + 1) m), GeneratesOn B m W τ →
      (∃ ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m,
        ∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
          IsPoincareResidue sX (N.n i ≫ ι) n m τ (ρ i)) ∧
      ∀ ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m,
        (∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
          IsPoincareResidue sX (N.n i ≫ ι) n m τ (ρ i)) →
        (∀ i, ρ i ≠ 0) →
        IsAdjointGeneratorOn N n m Θ (ι ⁻¹ᵁ W) ρ

/-- Each floor component maps to the floor by a closed immersion. -/
private theorem isClosedImmersion_floorComponent
    {hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents (ι ≫ sX) hfin) {Θ : ∀ i, QDivisor (N.X i)}
    (hΘ : ∀ i, IsAdjunctionStep sX B (N.n i ≫ ι) (Θ i)) (j : N.ι) : IsClosedImmersion (N.n j) :=
  haveI : IsClosedImmersion (N.n j ≫ ι) := (hΘ j).2.choose_spec.2.2.1
  IsClosedImmersion.of_comp (N.n j) ι

variable (hdim : topologicalKrullDim X = (n + 1 : ℕ)) (hK : K.IsCanonicalDivisor sX (n + 1))
  (hproj : MMP.Mori.IsProjectiveVariety k sX) (hQ : IsQFactorial sX)
  (hB : MMP.Fourfold.IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
  (hB0 : B.roundDown ≠ 0)
  (hT : Set.range ι.base = ⋃ P ∈ B.roundDown.support, (P.support : Set X))

include hdim hK hproj hQ hB hdlt hB0 hT

/-- **The floor is Cohen–Macaulay.** The ideal of `T` is `𝒪_X(-T)`; both it and `𝒪_X` are
Cohen–Macaulay, and the depth lemma in `0 → 𝒪_X(-T) → 𝒪_X → 𝒪_T → 0` concludes. -/
private theorem isCMScheme_floor : IsCMScheme T := by
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  haveI : MMP.Mori.IsProjectiveVariety k sX := hproj
  have hdltM : MMP.Mori.IsDltPair sX (n + 1) K B :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK B).mp hdlt
  have hCM : ∀ D : Divisor X, IsCMSheaf D.divisorialSheaf := fun D => by
    obtain ⟨m, hm, hmD⟩ := hQ.2 D
    refine MMP.Mori.isCMSheaf_divisorialSheaf_of_isDltPair sX hdltM
      ⟨m, by exact_mod_cast hm.ne', ?_⟩
    exact ⟨(m : ℤ) • D, by rw [map_zsmul], hmD⟩
  intro t
  refine isCMModule_of_linearEquiv (unitStalkLinearEquiv T.presheaf t).symm ?_
  have hR : IsCMModule (X.presheaf.stalk (ι.base t)) (X.presheaf.stalk (ι.base t)) :=
    isCMModule_of_linearEquiv ((stalkLinearEquiv Divisor.divisorialSheafZeroIso (ι.base t)).trans
      (unitStalkLinearEquiv X.presheaf (ι.base t))) (hCM 0 (ι.base t))
  obtain ⟨e⟩ := nonempty_stalk_divisorialSheaf_roundDown_linearEquiv_ker ι hB.nonneg hdlt.2.1 hT t
  have hI := isCMModule_of_linearEquiv e (hCM (-B.roundDown) (ι.base t))
  have hgen : genericPoint X ∉ Set.range ι.base := by
    rw [hT]
    simp only [Set.mem_iUnion, not_exists]
    intro P _ hP
    exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support P hP
  haveI : IsDomain (X.presheaf.stalk (ι.base t)) := IsNormal.stalk_isDomain _
  exact isCMModule_of_surjective_of_isCMModule_ker (ι.stalkMap t).hom
    (ι.stalkMap_surjective t) (ker_stalkMap_ne_bot ι hgen t) hR hI

/-- **The floor components.** The prime components `Tᵢ` of `⌊B⌋` are normal, they form the
normalization of `T`, and each carries its adjunction pair `(Tᵢ, Diff_{Tᵢ}(B - Tᵢ))`. -/
private theorem exists_normalizationComponents_isAdjunctionStep :
    ∃ (hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite)
      (N : NormalizationComponents (ι ≫ sX) hfin) (Θ : ∀ i, QDivisor (N.X i)),
      (∀ i, IsAdjunctionStep sX B (N.n i ≫ ι) (Θ i)) ∧
      (∀ P ∈ B.roundDown.support,
        ∃! i, Set.range (N.n i ≫ ι).base = (P.support : Set X)) := by
  have hlft : LocallyOfFiniteType sX := hB.isPair.1.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)
  have hfin := finite_irreducibleComponents_of_isLocallyNoetherian T
  let I := {P // P ∈ B.roundDown.support}
  choose S j BS hj hstep using
    fun P : I => exists_isAdjunctionStep_of_mem_roundDown_support hdim hB hdlt P.2
  haveI hint : ∀ P, IsIntegral (S P) := fun P => (hstep P).1.1.toIsIntegral
  haveI hnorm : ∀ P, IsNormal (S P) := fun P => (hstep P).1.2
  haveI hcl : ∀ P, IsClosedImmersion (j P) := fun P => (hstep P).2.choose_spec.2.2.1
  have hsub : ∀ P, Set.range (j P) ⊆ Set.range ι := fun P => by
    rw [hj P, hT]
    exact Set.subset_biUnion_of_mem (u := fun Q : MMP.Mori.PrimeDivisor X => (Q.support : Set X))
      P.2
  let nP : ∀ P, S P ⟶ T := fun P =>
    IsClosedImmersion.lift ι (j P) (ker_le_ker_of_range_subset ι (j P) (hsub P))
  have hnP : ∀ P, nP P ≫ ι = j P := fun P => IsClosedImmersion.lift_fac _ _ _
  haveI : ∀ P, IsClosedImmersion (nP P) := fun P =>
    have : IsClosedImmersion (nP P ≫ ι) := by rw [hnP]; infer_instance
    IsClosedImmersion.of_comp (nP P) ι
  have hrc := range_mem_irreducibleComponents_of_floor ι hT S nP (fun P : I => P.1)
    (fun P => P.2) Subtype.val_injective (fun Q hQ => ⟨⟨Q, hQ⟩, rfl⟩)
    (fun P => by rw [hnP]; exact hj P)
  have hloc : ∀ P, IsLocallyNoetherian (S P) := fun P =>
    haveI := (hstep P).1.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (j P ≫ sX)
  haveI : IsLocallyNoetherian (∐ S : Scheme.{0}) :=
    (isLocallyNoetherian_iff_openCover (sigmaOpenCover S)).mpr fun P =>
      hloc P
  obtain ⟨φ, hφ⟩ := exists_iso_normalizationScheme hfin S nP
    (finite_irreducibleComponents_of_isLocallyNoetherian _) hrc.1 hrc.2
  let N : NormalizationComponents (ι ≫ sX) hfin :=
    { ι := I
      X := S
      n := nP
      isNormalVariety := fun P => by
        rw [← Category.assoc, hnP]
        exact (hstep P).1
      exists_iso := ⟨φ, hφ⟩ }
  refine ⟨hfin, N, BS, fun P => ?_, fun Q hQ => ?_⟩
  · change IsAdjunctionStep sX B (nP P ≫ ι) (BS P)
    rw [hnP]
    exact hstep P
  · refine ⟨⟨Q, hQ⟩, ?_, fun P hP => ?_⟩
    · change Set.range (nP ⟨Q, hQ⟩ ≫ ι).base = _
      rw [hnP]
      exact hj _
    · change Set.range (nP P ≫ ι).base = _ at hP
      rw [hnP, hj P] at hP
      exact Subtype.ext (primeDivisor_eq_of_support_eq hP)

variable {hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
  (N : NormalizationComponents (ι ≫ sX) hfin) (Θ : ∀ i, QDivisor (N.X i))
  (hΘ : ∀ i, IsAdjunctionStep sX B (N.n i ≫ ι) (Θ i))
  (huniq : ∀ P ∈ B.roundDown.support,
    ∃! i, Set.range (N.n i ≫ ι).base = (P.support : Set X))

include hΘ huniq

/-- The floor components are indexed by the prime components of `⌊B⌋`. -/
private theorem exists_primeDivisor_floorComponent :
    ∃ P : N.ι → MMP.Mori.PrimeDivisor X,
      (∀ i, Set.range (N.n i ≫ ι).base = ((P i).support : Set X)) ∧
      (∀ i, P i ∈ B.roundDown.support) ∧ Function.Injective P ∧
      ∀ Q ∈ B.roundDown.support, ∃ i, P i = Q := by
  choose P hP using fun i => (hΘ i).2
  have hPrange : ∀ i, Set.range (N.n i ≫ ι) = ((P i).support : Set X) := fun i => (hP i).2.1
  have hPmem : ∀ i, P i ∈ B.roundDown.support := fun i =>
    mem_roundDown_support_of_one_le_coeff (hP i).1
  have hPinj : Function.Injective P := fun i j hij => by
    obtain ⟨l, -, hl⟩ := huniq (P i) (hPmem i)
    rw [hl i (hPrange i), hl j (show _ = _ by rw [hPrange j, hij])]
  have hPsurj : ∀ Q ∈ B.roundDown.support, ∃ i, P i = Q := fun Q hQ => by
    obtain ⟨i, hi, -⟩ := huniq Q hQ
    exact ⟨i, primeDivisor_eq_of_support_eq (by rw [← hPrange i]; exact hi)⟩
  exact ⟨P, hPrange, hPmem, hPinj, hPsurj⟩

/-- Every point of the floor lies on a floor component. -/
private theorem exists_mem_range_floorComponent (t : T) : ∃ i, t ∈ Set.range (N.n i).base := by
  obtain ⟨P, hPr, -, -, hPs⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  have ht : ι.base t ∈ Set.range ι.base := ⟨t, rfl⟩
  rw [hT] at ht
  obtain ⟨_, ⟨Q, rfl⟩, ht⟩ := ht
  obtain ⟨hQ, htQ⟩ := Set.mem_iUnion.mp ht
  obtain ⟨i, rfl⟩ := hPs Q hQ
  rw [← hPr i] at htQ
  obtain ⟨y, hy⟩ := htQ
  exact ⟨i, y, ι.isClosedEmbedding.injective (by rw [← hy]; rfl)⟩

/-- Each floor component has dimension `n`. -/
private theorem topologicalKrullDim_floorComponent (i : N.ι) :
    topologicalKrullDim (N.X i) = (n : ℕ) := by
  obtain ⟨P, hPr, -, -, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : IsClosedImmersion (N.n i ≫ ι) := (hΘ i).2.choose_spec.2.2.1
  have e2 : topologicalKrullDim (N.X i) = topologicalKrullDim (Set.range (N.n i ≫ ι)) :=
    (N.n i ≫ ι).isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  rw [e2, hPr i]
  have hlft : LocallyOfFiniteType sX := hB.isPair.1.1.toLocallyOfFiniteType
  have h1 := topologicalKrullDim_support_add_one sX (P i)
  rw [hdim] at h1
  exact eq_natCast_of_add_one_eq_natCast_succ h1

/-- **A prime divisor of a floor component has codimension one in the floor.** -/
private theorem coheight_floorComponent_primeDivisor (i : N.ι)
    (Q : MMP.Mori.PrimeDivisor (N.X i)) :
    Order.coheight ((N.n i).base Q.genericPoint) = 1 := by
  haveI : IsClosedImmersion (N.n i ≫ ι) := (hΘ i).2.choose_spec.2.2.1
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  have hlft : ∀ j, LocallyOfFiniteType (N.n j ≫ ι ≫ sX) := fun j =>
    (N.isNormalVariety j).1.toLocallyOfFiniteType
  have hdimj := topologicalKrullDim_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  set y := (N.n i).base Q.genericPoint with hy
  -- the dimension of the closure of `y`
  have hdy : topologicalKrullDim (closure {y} : Set T) + 1 = (n : WithBot ℕ∞) := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (N.n i ≫ ι ≫ sX)
      Q.genericPoint
    rw [Q.coheight_genericPoint, hdimj i] at h
    have himg : (N.n i).base '' closure {Q.genericPoint} = closure {y} := by
      rw [← (N.n i).isClosedEmbedding.closure_image_eq, Set.image_singleton]
    rw [← himg, ← ((N.n i).isClosedEmbedding.isEmbedding.homeomorphImage
      (closure {Q.genericPoint})).isHomeomorph.topologicalKrullDim_eq]
    exact_mod_cast h
  refine le_antisymm ?_ ?_
  · by_contra hlt
    have h2 : ((2 : ℕ) : ℕ∞) ≤ Order.coheight y := by
      rw [not_le] at hlt
      exact Order.add_one_le_of_lt hlt
    obtain ⟨p, hp0, hplen⟩ := Order.exists_series_of_le_coheight y h2
    have h01 : p ⟨0, by omega⟩ < p ⟨1, by omega⟩ := p.strictMono (by simp [Fin.lt_def])
    have h12 : p ⟨1, by omega⟩ < p ⟨2, by omega⟩ := p.strictMono (by simp [Fin.lt_def])
    obtain ⟨j, q2, hq2⟩ := exists_mem_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
      hΘ huniq (p ⟨2, by omega⟩)
    have hcl : ∀ z : T, p ⟨2, by omega⟩ ⤳ z → z ∈ Set.range (N.n j).base := fun z hz =>
      (N.n j).isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr ⟨q2, hq2⟩) (specializes_iff_mem_closure.mp hz)
    obtain ⟨q1, hq1⟩ := hcl _ h12.le
    obtain ⟨q0, hq0⟩ := hcl _ (h01.le.trans h12.le)
    have hsp : ∀ {a b : N.X j}, (N.n j).base a ⤳ (N.n j).base b → a ⤳ b := fun h =>
      ((N.n j).isClosedEmbedding.isInducing.specializes_iff).mp h
    have hl01 : q0 < q1 :=
      MMP.Intersection.lt_of_specializes_of_ne (hsp (by rw [hq0, hq1]; exact h01.le))
      (fun h => h01.ne (by rw [← hq0, ← hq1, h]))
    have hl12 : q1 < q2 :=
      MMP.Intersection.lt_of_specializes_of_ne (hsp (by rw [hq1, hq2]; exact h12.le))
      (fun h => h12.ne (by rw [← hq1, ← hq2, h]))
    have hc0 : (2 : ℕ∞) ≤ Order.coheight q0 := by
      have a := Order.coheight_add_one_le hl12
      have b := Order.coheight_add_one_le hl01
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ Order.coheight q2 + 1 + 1 := by gcongr; exact bot_le
        _ ≤ Order.coheight q1 + 1 := by gcongr
        _ ≤ Order.coheight q0 := b
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (N.n j ≫ ι ≫ sX) q0
    rw [hdimj j] at h
    have himg : (N.n j).base '' closure {q0} = closure {y} := by
      rw [← (N.n j).isClosedEmbedding.closure_image_eq, Set.image_singleton, hq0, ← hp0]
      rfl
    rw [((N.n j).isClosedEmbedding.isEmbedding.homeomorphImage
      (closure {q0})).isHomeomorph.topologicalKrullDim_eq, himg] at h
    -- `dim closure {y} = n - 1` and `coheight q0 ≥ 2` contradict `dim + coheight = n`
    induction hd : topologicalKrullDim (closure {y} : Set T) using WithBot.recBotCoe with
    | bot => rw [hd, WithBot.bot_add] at hdy; exact WithBot.bot_ne_coe hdy
    | coe d =>
      rw [hd] at hdy h
      have h' : d + Order.coheight q0 = n := by exact_mod_cast h
      have hdy' : d + 1 = n := by exact_mod_cast hdy
      have : d + 2 ≤ d + 1 := by
        calc d + 2 ≤ d + Order.coheight q0 := by gcongr
          _ = d + 1 := by rw [h', hdy']
      induction d using ENat.recTopCoe with
      | top => simp at hdy'
      | coe d => norm_cast at this; omega
  · -- the generic point of the component strictly generizes `y`
    have hne : Q.genericPoint ≠ genericPoint (N.X i) := by
      intro h
      apply MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support Q
      rw [← h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hlt : y < (N.n i).base (genericPoint (N.X i)) :=
      MMP.Intersection.lt_of_specializes_of_ne
        ((genericPoint_specializes Q.genericPoint).map (N.n i).base.hom.continuous)
        (fun h => hne ((N.n i).isClosedEmbedding.injective h))
    exact le_add_self.trans (Order.coheight_add_one_le hlt)

/-- At a point lying on a single floor component, the stalk of the floor is the stalk of the
component. -/
private theorem bijective_stalkMap_floorComponent (i : N.ι) (t : N.X i)
    (ht : ∀ j, j ≠ i → (N.n i).base t ∉ Set.range (N.n j).base) :
    Function.Bijective ((N.n i).stalkMap t).hom := by
  classical
  obtain ⟨P, -, hPmem, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : Finite N.ι := Finite.of_injective
    (fun i => (⟨P i, hPmem i⟩ : {Q // Q ∈ B.roundDown.support}))
    fun a b h => hPinj (congrArg Subtype.val h)
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  let V : T.Opens := ⟨(⋃ j ∈ ({i}ᶜ : Set N.ι), Set.range (N.n j).base)ᶜ, by
    refine (Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ =>
      (N.n j).isClosedEmbedding.isClosed_range).isOpen_compl⟩
  have htV : (N.n i).base t ∈ V := by
    simp only [V, TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact ht
  have hV : (V : Set T) ⊆ Set.range (N.n i).base := by
    intro z hz
    obtain ⟨j, hj⟩ := exists_mem_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
      hΘ huniq z
    by_cases hji : j = i
    · exact hji ▸ hj
    · exact absurd (Set.mem_iUnion₂.mpr ⟨j, hji, hj⟩) hz
  exact ⟨stalkMap_injective_of_subset_range (N.n i) t V htV hV, (N.n i).stalkMap_surjective t⟩

/-- **Dlt adjunction to a floor component**, in the sense of log discrepancies. -/
private theorem isDltPair_floorComponent (i : N.ι) :
    MMP.Intersection.IsDltPair (N.n i ≫ ι ≫ sX) (Θ i) := by
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  obtain ⟨P, hP1, hPr, hcl, -⟩ := (hΘ i).2
  have hPmem : P ∈ B.roundDown.support := mem_roundDown_support_of_one_le_coeff hP1
  have hstep : IsAdjunctionStep (𝟙 X ≫ sX) B (N.n i ≫ ι) (Θ i) := by
    rw [Category.id_comp]; exact hΘ i
  let F : StratumAdjunctionData sX B ((N.n i ≫ ι) ≫ 𝟙 X) (Θ i) :=
    .step (.refl hB.isPair) _ _ hstep
  have hd := (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair
    (isDltStratum_support hB hdlt hPmem)).1.2 F (by rw [Category.comp_id]; exact hPr)
  simpa using hd

/-- **The boundary of a floor component is `1` along the double locus.** If a prime divisor `Q` of
`Tᵢ` maps into a second floor component `Tⱼ`, then `coeff_Q Θᵢ = 1`. -/
private theorem coeff_eq_one_of_mem_range (i j : N.ι) (hij : j ≠ i)
    (Q : MMP.Mori.PrimeDivisor (N.X i))
    (hQr : (N.n i).base Q.genericPoint ∈ Set.range (N.n j).base) : (Θ i).coeff Q = 1 := by
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  obtain ⟨P, hPr, hPmem, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  have hd := isDltPair_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i
  refine le_antisymm (hd.2.1 Q) ?_
  have hPj1 : 1 ≤ B.coeff (P j) :=
    (coeff_eq_one_of_mem_roundDown_support hB.nonneg hdlt.2.1 (hPmem j)).ge
  have hWQ : (Q.support : Set (N.X i)) ⊆ (N.n i ≫ ι).base ⁻¹' ((P j).support : Set X) := by
    intro w hw
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hw
    have hsp : Q.genericPoint ⤳ w := specializes_iff_mem_closure.mpr hw
    have hcl : IsClosed ((P j).support : Set X) := (P j).idealSheaf.support.isClosed
    refine hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ?_)
      (specializes_iff_mem_closure.mp (hsp.map (N.n i ≫ ι).base.hom.continuous))
    obtain ⟨q, hq⟩ := hQr
    rw [← hPr j]
    exact ⟨q, by rw [Scheme.Hom.comp_base, TopCat.comp_app, hq]; rfl⟩
  have hirr : IsIrreducible (Q.support : Set (N.X i)) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  obtain ⟨Q', hQQ', -, hQ'1⟩ := exists_primeDivisor_of_isAdjunctionStep hdlt (hΘ i) (hPr i)
    (fun h => hij (hPinj h)) hPj1 hirr hWQ
  have : Q' = Q := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support (hQQ' (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl))
  rw [← this]
  exact hQ'1

/-- The image of the generic point of a floor component is the generic point of an irreducible
component of the floor. -/
private theorem closure_mem_irreducibleComponents_floorComponent (i : N.ι) :
    closure {(N.n i).base (genericPoint (N.X i))} ∈ irreducibleComponents T := by
  obtain ⟨P, hPr, hPmem, hPinj, hPs⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  have h := (range_mem_irreducibleComponents_of_floor ι hT N.X N.n P hPmem hPinj hPs hPr).1 i
  rwa [← Set.image_singleton, (N.n i).isClosedEmbedding.closure_image_eq,
    (genericPoint_spec (N.X i)).def, Set.image_univ]

/-- The generic point of a floor component has codimension zero in the floor. -/
private theorem coheight_genericPoint_floorComponent (i : N.ι) :
    Order.coheight ((N.n i).base (genericPoint (N.X i))) = 0 := by
  rw [Order.coheight_eq_zero]
  intro z hz
  have hc := closure_mem_irreducibleComponents_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT
    N Θ hΘ huniq i
  have hsub : closure {(N.n i).base (genericPoint (N.X i))} ⊆ closure {z} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hz))
      isClosed_closure
  have := hc.2 isIrreducible_singleton.closure hsub
  exact specializes_iff_mem_closure.mpr (this (subset_closure rfl))

/-- A codimension-one point on a single floor component is a regular point of the floor. -/
private theorem isRegularLocalRing_stalk_of_single (i : N.ι) (t : N.X i)
    (ht1 : Order.coheight t = 1)
    (ht : ∀ j, j ≠ i → (N.n i).base t ∉ Set.range (N.n j).base) :
    IsRegularLocalRing (T.presheaf.stalk ((N.n i).base t)) := by
  set E := AlgebraicGeometry.PrimeDivisor.ofCoheightOne t ht1
  have hE : E.genericPoint = t := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hdvr := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing (X := N.X i) E
  have hreg : IsRegularLocalRing ((N.X i).presheaf.stalk t) := by
    rw [← hE]
    infer_instance
  have hbij := bijective_stalkMap_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
    i t ht
  exact IsRegularLocalRing.of_ringEquiv (RingEquiv.ofBijective _ hbij).symm

/-- A point on a single floor component is not in the double locus. -/
private theorem notMem_doubleIntersectionLocus_of_single (i : N.ι) (t : N.X i)
    (ht : ∀ j, j ≠ i → (N.n i).base t ∉ Set.range (N.n j).base) :
    (N.n i).base t ∉ (doubleIntersectionLocus T : Set T) := by
  classical
  obtain ⟨P, -, hPmem, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : Finite N.ι := Finite.of_injective
    (fun i => (⟨P i, hPmem i⟩ : {Q // Q ∈ B.roundDown.support}))
    fun a b h => hPinj (congrArg Subtype.val h)
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  let V : Set T := (⋃ j ∈ ({i}ᶜ : Set N.ι), Set.range (N.n j).base)ᶜ
  have hVo : IsOpen V := (Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ =>
      (N.n j).isClosedEmbedding.isClosed_range).isOpen_compl
  have htV : (N.n i).base t ∈ V := by
    simp only [V, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact ht
  intro hmem
  obtain ⟨s, hsV, hsS⟩ := mem_closure_iff.mp hmem V hVo htV
  obtain ⟨hs1, hsreg⟩ := hsS
  obtain ⟨j, s', rfl⟩ := exists_mem_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
    hΘ huniq s
  have hji : j = i := by
    by_contra h
    exact hsV (Set.mem_iUnion₂.mpr ⟨j, h, s', rfl⟩)
  subst hji
  have hsingle : ∀ l, l ≠ j → (N.n j).base s' ∉ Set.range (N.n l).base := fun l hl h =>
    hsV (Set.mem_iUnion₂.mpr ⟨l, hl, h⟩)
  -- the codimension of `s'` in its component is one
  have hmono : StrictMono (N.n j).base := fun a b hab =>
    MMP.Intersection.lt_of_specializes_of_ne (hab.le.map (N.n j).base.hom.continuous)
      (fun h => hab.ne ((N.n j).isClosedEmbedding.injective h))
  have hle := Order.coheight_le_coheight_apply_of_strictMono _ hmono s'
  rw [hs1] at hle
  have hne : s' ≠ genericPoint (N.X j) := by
    rintro rfl
    rw [coheight_genericPoint_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq j]
      at hs1
    exact zero_ne_one hs1
  have hge : 1 ≤ Order.coheight s' := by
    have hlt : s' < genericPoint (N.X j) :=
      MMP.Intersection.lt_of_specializes_of_ne (genericPoint_specializes s') hne
    exact le_add_self.trans (Order.coheight_add_one_le hlt)
  exact hsreg (isRegularLocalRing_stalk_of_single ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
    j s' (le_antisymm hle hge) hsingle)

/-- A point of a floor component lying on a second component is in the double locus. -/
private theorem mem_doubleIntersectionLocus_of_mem_range (i j : N.ι) (hij : j ≠ i)
    (Q : MMP.Mori.PrimeDivisor (N.X i))
    (hQr : (N.n i).base Q.genericPoint ∈ Set.range (N.n j).base) :
    (N.n i).base Q.genericPoint ∈ (doubleIntersectionLocus T : Set T) := by
  obtain ⟨P, hPr, -, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  apply subset_closure
  refine ⟨coheight_floorComponent_primeDivisor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i Q,
    fun hreg => ?_⟩
  haveI := hreg
  haveI : IsDomain (T.presheaf.stalk ((N.n i).base Q.genericPoint)) :=
    IsRegularLocalRing.isDomain _
  obtain ⟨q, hq⟩ := hQr
  have hc := closure_mem_irreducibleComponents_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT
    N Θ hΘ huniq
  have heq := eq_of_isDomain_stalk (hc i) (hc j)
    ((genericPoint_specializes Q.genericPoint).map (N.n i).base.hom.continuous)
    (hq ▸ (genericPoint_specializes q).map (N.n j).base.hom.continuous)
  -- equal generic points give equal components
  have hrange : ∀ l, Set.range (N.n l).base = closure {(N.n l).base (genericPoint (N.X l))} :=
    fun l => by
      rw [← Set.image_singleton, (N.n l).isClosedEmbedding.closure_image_eq,
        (genericPoint_spec (N.X l)).def, Set.image_univ]
  have hPP : ((P i).support : Set X) = (P j).support := by
    rw [← hPr i, ← hPr j, Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp,
      TopCat.coe_comp, Set.range_comp, Set.range_comp, hrange i, hrange j, heq]
  exact hij (hPinj (primeDivisor_eq_of_support_eq hPP)).symm

/-- The floor is an `n`-fold: it is separated of finite type over `k`, reduced, and each of
its irreducible components, a prime component of `⌊B⌋`, has dimension `n`. -/
private theorem isNFold_floor : IsNFold (ι ≫ sX) n := by
  have hv := hproj.toIsVariety
  haveI : LocallyOfFiniteType sX := hv.toLocallyOfFiniteType
  haveI : IsSeparated sX := hv.toIsSeparated
  haveI : QuasiCompact sX := hv.toQuasiCompact
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, fun Z hZ => ?_⟩
  obtain ⟨P, hPr, hPmem, hPinj, hPs⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  obtain ⟨i, rfl, -⟩ :=
    (range_mem_irreducibleComponents_of_floor ι hT N.X N.n P hPmem hPinj hPs hPr).2 Z hZ
  haveI : IsClosedImmersion (N.n i ≫ ι) := (hΘ i).2.choose_spec.2.2.1
  haveI : IsClosedImmersion (N.n i) := IsClosedImmersion.of_comp (N.n i) ι
  rw [← (N.n i).isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact topologicalKrullDim_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i

/-- **Residue adjunction along a floor component.** The residues of a local generator of
`𝒪_X(m(K_X + B))` on `W` along a floor component `Tᵢ` meeting `W` exist, and every such residue
generates `𝒪_{Tᵢ}(m(K_{Tᵢ} + Θᵢ))` over `W`. -/
private theorem exists_isPoincareResidue_and_generatesOn (i : N.ι) {m : ℕ} (hm : 0 < m)
    (hC : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    {W : X.Opens} {τ : RationalPluriForms sX (n + 1) m} (hτ : GeneratesOn B m W τ)
    (hW : ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty) :
    (∃ ρ, IsPoincareResidue sX (N.n i ≫ ι) n m τ ρ) ∧
      ∀ ρ, IsPoincareResidue sX (N.n i ≫ ι) n m τ ρ →
        GeneratesOn (Θ i) m ((N.n i) ⁻¹ᵁ (ι ⁻¹ᵁ W)) ρ := by
  classical
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  obtain ⟨P, hPr, hPmem, -, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  set j := N.n i ≫ ι with hj
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : CompactSpace X := haveI := hXv.1; QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsClosedImmersion j := (hΘ i).2.choose_spec.2.2.1
  have hTv : IsNormalVariety k (j ≫ sX) := by rw [hj, Category.assoc]; exact N.isNormalVariety i
  haveI : LocallyOfFiniteType (j ≫ sX) := hTv.1.toLocallyOfFiniteType
  haveI : CompactSpace (N.X i) := haveI := hTv.1;
    QuasiCompact.compactSpace_of_compactSpace (j ≫ sX)
  have hdimX : topologicalKrullDim X = n + 1 := by rw [hdim]; push_cast; rfl
  have hdimT : topologicalKrullDim (N.X i) = n :=
    topologicalKrullDim_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i
  have hBP : B.coeff (P i) = 1 := coeff_eq_one_of_mem_roundDown_support hB.nonneg hdlt.2.1 (hPmem i)
  set B' : QDivisor X := B - Finsupp.single (P i) 1 with hB'
  have hBY : B = Finsupp.single (P i) 1 + B' := by rw [hB']; abel
  obtain ⟨τ₁, hτ₁0, hτ₁P, ρ₁, hρ₁, hρ₁0⟩ :=
    exists_ordForm_eq_neg_one_isPoincareResidue_of_charZero sX hdimX j (P i) (hPr i)
  have hlin := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hK hτ₁0
  rw [one_smul] at hlin
  have hQK : (Divisor.toQDivisor K + B).IsQCartier := ⟨m, by exact_mod_cast hm.ne', hC⟩
  have hDq : (Divisor.toQDivisor (divisorOfForm τ₁) + B).IsQCartier :=
    hQK.add_of_linearlyEquivalent hlin.symm
  obtain ⟨hgen₁, hpb₁⟩ :=
    (hΘ i).isPullback_divisorOfForm_add_of_isPoincareResidue hdimX (P i) (hPr i) τ₁ hτ₁0 hτ₁P ρ₁
      hρ₁ hDq
  have hgen : ∀ Z : irreducibleComponents (N.X i), j (componentGenericPoint (N.X i) Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ₁) + Finsupp.single (P i) 1 + B').supp := by
    rw [add_assoc, ← hBY]; exact hgen₁
  have hpb : (Divisor.toQDivisor (divisorOfForm τ₁) + Finsupp.single (P i) 1 + B').IsPullback j
      hgen (Divisor.toQDivisor (divisorOfForm ρ₁) + Θ i) :=
    isPullback_congr hpb₁ (by rw [add_assoc, ← hBY]) rfl
  obtain ⟨DM, hDM, hDMc⟩ := isCartierDivisor_smul_add_of_linearlyEquivalent hC hlin.symm
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  have hDM' : Divisor.toQDivisor DM = ((M + 1 : ℕ) : ℤ) •
      (Divisor.toQDivisor (divisorOfForm τ₁) + Finsupp.single (P i) 1 + B') := by
    rw [hDM, add_assoc, ← hBY]
  have hgens := MMP.CyclicChartDifferent.Aux.exists_generatesOn_isPoincareResidue sX hdimX j hTv
    hdimT (P i) (hPr i) B' τ₁ hτ₁0 ρ₁ hρ₁ hρ₁0 (Θ i) hgen hpb M DM hDM' hDMc
  letI := functionFieldAlgebra sX
  have hd : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdimX]; norm_cast)
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) (d := n + 1) (by rw [hdimX]; norm_cast)
  have hrank : Module.finrank X.functionField
      (RationalPluriForms sX (n + 1) ((M + 1 : ℕ) : ℤ)) = 1 := by
    let bb : Module.Basis Unit X.functionField
        (RationalPluriForms sX (n + 1) ((M + 1 : ℕ) : ℤ)) := ZTensorPower.basis b₀ ((M + 1 : ℕ) : ℤ)
    rw [Module.finrank_eq_card_basis bb]
    rfl
  -- comparison of `τ` with a local generator whose residue generates
  have hcmp : ∀ x : N.X i, j.base x ∈ W → ∃ (U : X.Opens) (_ : j.base x ∈ U)
      (ρ' : RationalPluriForms (j ≫ sX) n ((M + 1 : ℕ) : ℤ))
      (u : X.presheaf.stalk (j (genericPoint (N.X i)))), IsUnit u ∧
      IsPoincareResidue sX j n (M + 1) τ ((j.stalkMap (genericPoint (N.X i))).hom u • ρ') ∧
      GeneratesOn (Θ i) (M + 1) (j ⁻¹ᵁ U) ρ' ∧
      ∀ Q : MMP.Mori.PrimeDivisor (N.X i), j.base Q.genericPoint ∈ U ⊓ W →
        (N.X i).ord ((j.stalkMap (genericPoint (N.X i))).hom u) Q.genericPoint = 0 := by
    intro x hxW
    obtain ⟨U, hxU, τ', hτ', ρ', hρ', hρ'g⟩ := hgens x
    rw [← hBY] at hτ'
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' τ' hτ'.1).mp hrank τ
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hτ.1 hc.symm
    -- `c` has no zeros or poles on `U ∩ W`
    have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ (U ⊓ W : X.Opens)).Nonempty →
        X.ord c Γ.genericPoint = 0 := by
      intro Γ hΓ
      have h1 := hτ.2 Γ (hΓ.mono (Set.inter_subset_inter_right _ inf_le_right))
      have h2 := hτ'.2 Γ (hΓ.mono (Set.inter_subset_inter_right _ inf_le_left))
      rw [← hc, Γ.ordForm_smul hd hc0 hτ'.1] at h1
      push_cast at h1 h2
      exact_mod_cast (by linarith : ((X.ord c Γ.genericPoint : ℤ) : ℚ) = 0)
    have hunit : ∀ y : X, y ∈ U ⊓ W → ∃ a : X.presheaf.stalk y, IsUnit a ∧
        algebraMap (X.presheaf.stalk y) X.functionField a = c := fun y hy =>
      MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero y hc0 fun Γ hΓ =>
        hord Γ ⟨y, hΓ, hy⟩
    have hgenU : j (genericPoint (N.X i)) ∈ U ⊓ W :=
      ((genericPoint_specializes x).map j.base.hom.continuous).mem_open (U ⊓ W).isOpen
        ⟨hxU, hxW⟩
    obtain ⟨u, hu, hu'⟩ := hunit _ hgenU
    refine ⟨U, hxU, ρ', u, hu, ?_, hρ'g, fun Q hQ => ?_⟩
    · rw [← hc, ← hu']
      exact MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ' u
    · obtain ⟨v, hv, hv'⟩ := hunit _ hQ
      have hsp : j (genericPoint (N.X i)) ⤳ j Q.genericPoint :=
        (genericPoint_specializes Q.genericPoint).map j.base.hom.continuous
      have huv : (X.presheaf.stalkSpecializes hsp).hom v = u :=
        IsFractionRing.injective (X.presheaf.stalk (j (genericPoint (N.X i)))) X.functionField
          (by rw [MMP.Mori.algebraMap_stalkSpecializes, hv', hu'])
      rw [← huv, Scheme.Hom.stalkSpecializes_stalkMap_apply]
      exact ord_algebraMap_eq_zero_of_isUnit Q rfl (hv.map _)
  letI := functionFieldAlgebra (j ≫ sX)
  have hdT : (Algebra.trdeg k (N.X i).functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := j ≫ sX) hdimT
  obtain ⟨x₀, hx₀⟩ := hW
  obtain ⟨U₀, hxU₀, ρ₀, u₀, hu₀, hres₀, hρ₀g, -⟩ := hcmp x₀ hx₀
  refine ⟨⟨_, hres₀⟩, fun ρ hρ => ⟨?_, fun Q hQ => ?_⟩⟩
  · rw [IsPoincareResidue.unique (hΘ i) hρ hres₀]
    exact smul_ne_zero (hu₀.map _).ne_zero hρ₀g.1
  · obtain ⟨z, hzQ, hzW⟩ := hQ
    have hzW' : j.base z ∈ W := hzW
    obtain ⟨U, hzU, ρ', u, hu, hres, hρ'g, hordQ⟩ := hcmp z hzW'
    rw [IsPoincareResidue.unique (hΘ i) hρ hres]
    have hQz : Q.genericPoint ⤳ z := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hzQ
      exact specializes_iff_mem_closure.mpr hzQ
    have hQUW : j.base Q.genericPoint ∈ U ⊓ W :=
      (hQz.map j.base.hom.continuous).mem_open (U ⊓ W).isOpen ⟨hzU, hzW'⟩
    rw [Q.ordForm_smul hdT ((hu.map _).ne_zero) hρ'g.1, hordQ Q hQUW, zero_add]
    exact hρ'g.2 Q ⟨z, hzQ, hzU⟩

/-- **A double point of the floor lies in the snc locus.** If a prime divisor `Q` of `Tᵢ` maps
into a second floor component `Tⱼ`, the image of its generic point in `X` is not in the bad set
`Z` of the dlt condition. -/
private theorem notMem_badSet_of_mem_range (i j : N.ι) (hij : j ≠ i)
    (Q : MMP.Mori.PrimeDivisor (N.X i))
    (hQr : (N.n i).base Q.genericPoint ∈ Set.range (N.n j).base)
    {Z : TopologicalSpace.Closeds X}
    (hpos : ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Z →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) D a →
        0 < a) :
    ι.base ((N.n i).base Q.genericPoint) ∉ (Z : Set X) := by
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  obtain ⟨P, hPr, hPmem, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  haveI : IsClosedImmersion (N.n i ≫ ι) := (hΘ i).2.choose_spec.2.2.1
  set y := ι.base ((N.n i).base Q.genericPoint) with hy
  have hyi : y ∈ ((P i).support : Set X) := by rw [← hPr i]; exact ⟨Q.genericPoint, rfl⟩
  have hyj : y ∈ ((P j).support : Set X) := by
    obtain ⟨q, hq⟩ := hQr
    rw [← hPr j]; exact ⟨q, by rw [Scheme.Hom.comp_base, TopCat.comp_app, hq]⟩
  have hc1 := fun l => coeff_eq_one_of_mem_roundDown_support hB.nonneg hdlt.2.1 (hPmem l)
  intro hyZ
  obtain ⟨c, hcZ, hyc, hcPQ⟩ := exists_notMem_closure_of_isDltPair hdlt hpos
    (fun h => hij (hPinj h).symm) (hc1 i).ge (hc1 j).ge (isIrreducible_singleton.closure)
    (closure_minimal (Set.singleton_subset_iff.mpr ⟨hyi, hyj⟩)
      ((P i).idealSheaf.support.isClosed.inter (P j).idealSheaf.support.isClosed))
  -- `c` generizes `y` inside `Pᵢ ∩ Pⱼ`, so it is `y`
  have hcy : c ⤳ y := specializes_iff_mem_closure.mpr (hyc (subset_closure rfl))
  have hci : c ∈ Set.range (N.n i ≫ ι).base := by rw [hPr i]; exact (hcPQ (subset_closure rfl)).1
  obtain ⟨c', hc'⟩ := hci
  have hsp : c' ⤳ Q.genericPoint := by
    apply ((N.n i ≫ ι).isClosedEmbedding.isInducing.specializes_iff).mp
    rw [hc']; exact hcy
  by_cases hcQ : c' = Q.genericPoint
  · apply hcZ
    rw [← hc', hcQ]
    exact hyZ
  -- otherwise `Q` would have codimension at least two in `Tᵢ`
  have hne : c' ≠ genericPoint (N.X i) := by
    rintro rfl
    have : (N.n i ≫ ι).base (genericPoint (N.X i)) ∈ ((P j).support : Set X) :=
      hc' ▸ (hcPQ (subset_closure rfl)).2
    have hPP : P j = P i := by
      apply MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support
      have hg : (P i).genericPoint = (N.n i ≫ ι).base (genericPoint (N.X i)) := by
        have h1 : IsGenericPoint ((N.n i ≫ ι).base (genericPoint (N.X i)))
            ((P i).support : Set X) := by
          have := (genericPoint_spec (N.X i)).image (N.n i ≫ ι).base.hom.continuous
          rwa [Set.image_univ, (N.n i ≫ ι).isClosedEmbedding.isClosed_range.closure_eq,
            hPr i] at this
        have h2 : IsGenericPoint (P i).genericPoint ((P i).support : Set X) := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
        exact h2.eq h1
      rwa [hg]
    exact hij (hPinj hPP)
  have hl1 : Q.genericPoint < c' := MMP.Intersection.lt_of_specializes_of_ne hsp (Ne.symm hcQ)
  have hl2 : c' < genericPoint (N.X i) :=
    MMP.Intersection.lt_of_specializes_of_ne (genericPoint_specializes c') hne
  have a := Order.coheight_add_one_le hl2
  have b := Order.coheight_add_one_le hl1
  have : (2 : ℕ∞) ≤ Order.coheight Q.genericPoint := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint (N.X i)) + 1 + 1 := by gcongr; exact bot_le
      _ ≤ Order.coheight c' + 1 := by gcongr
      _ ≤ _ := b
  rw [Q.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- **Snc coordinates at a double point.** At the image `y ∈ X` of a branch point lying on the
floor components `Pᵢ ≠ Pⱼ`, the local ring `𝒪_{X,y}` has a regular system of parameters `x, y'`
cutting out `Pᵢ` and `Pⱼ`, and no other component of `B` passes through `y`. -/
private theorem exists_coordinates_of_mem_range (i j : N.ι) (hij : j ≠ i)
    (Q : MMP.Mori.PrimeDivisor (N.X i))
    (hQr : (N.n i).base Q.genericPoint ∈ Set.range (N.n j).base)
    {Pi Pj : MMP.Mori.PrimeDivisor X} (hPi : Set.range (N.n i ≫ ι).base = (Pi.support : Set X))
    (hPj : Set.range (N.n j ≫ ι).base = (Pj.support : Set X)) (hPij : Pi ≠ Pj)
    (hPim : Pi ∈ B.roundDown.support) (hPjm : Pj ∈ B.roundDown.support) :
    ∃ x y' : X.presheaf.stalk (ι.base ((N.n i).base Q.genericPoint)),
      IsRegularSystemOfParameters ![x, y'] ∧
      AlgebraicGeometry.IdealSheafData.stalk Pi.idealSheaf (ι.base ((N.n i).base Q.genericPoint)) =
        Ideal.span {x} ∧
      AlgebraicGeometry.IdealSheafData.stalk Pj.idealSheaf (ι.base ((N.n i).base Q.genericPoint)) =
        Ideal.span {y'} ∧
      ∀ Γ ∈ B.support, ι.base ((N.n i).base Q.genericPoint) ∈ Γ.support → Γ = Pi ∨ Γ = Pj := by
  classical
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  set y := ι.base ((N.n i).base Q.genericPoint) with hy
  obtain ⟨⟨hpair, hB0', -⟩, hB1, Z, -, hsnc, hpos⟩ := id hdlt
  have hyZ := notMem_badSet_of_mem_range ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i j hij Q
    hQr hpos
  rw [inverseTransformDivisor_ι_eq_restrictOpen] at hsnc
  set U : X.Opens := Z.compl
  have hyU : y ∈ U := hyZ
  obtain ⟨N₀, z, jj, hz, hjj, hI⟩ :=
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι B ⟨_, hyU⟩).mp
      (hsnc.2 ⟨_, hyU⟩)
  have hsupp : ∀ G ∈ B.roundDown.support, G ∈ B.support := fun _ hG =>
    mem_support_of_mem_roundDown_support hB.nonneg hdlt.2.1 hG
  have hyi : y ∈ (Pi.support : Set X) := by rw [← hPi]; exact ⟨Q.genericPoint, rfl⟩
  have hyj : y ∈ (Pj.support : Set X) := by
    obtain ⟨q, hq⟩ := hQr
    rw [← hPj]; exact ⟨q, by rw [Scheme.Hom.comp_base, TopCat.comp_app, hq]⟩
  -- the local ring at `y` has dimension two
  have hcoh : Order.coheight y = 2 := by
    have hlft : LocallyOfFiniteType sX := hpair.1.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sX) := (N.isNormalVariety i).1.toLocallyOfFiniteType
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX y
    have hQ1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (N.n i ≫ ι ≫ sX)
      Q.genericPoint
    rw [Q.coheight_genericPoint,
      topologicalKrullDim_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i] at hQ1
    haveI : IsClosedImmersion (N.n i ≫ ι) := (hΘ i).2.choose_spec.2.2.1
    have himg : (N.n i ≫ ι).base '' closure {Q.genericPoint} = closure {y} := by
      rw [← (N.n i ≫ ι).isClosedEmbedding.closure_image_eq, Set.image_singleton]; rfl
    rw [← himg, ← ((N.n i ≫ ι).isClosedEmbedding.isEmbedding.homeomorphImage
      (closure {Q.genericPoint})).isHomeomorph.topologicalKrullDim_eq, hdim] at h
    induction hd : topologicalKrullDim (closure {Q.genericPoint} : Set (N.X i))
      using WithBot.recBotCoe with
    | bot => rw [hd, WithBot.bot_add] at hQ1; exact absurd hQ1 WithBot.bot_ne_coe
    | coe d =>
      rw [hd] at hQ1 h
      induction d using ENat.recTopCoe with
      | top => exfalso; norm_cast at hQ1
      | coe d =>
        have e1 : d + 1 = n := by exact_mod_cast hQ1
        induction hc : Order.coheight y using ENat.recTopCoe with
        | top => rw [hc] at h; norm_cast at h
        | coe c =>
          rw [hc] at h
          have e2 : d + c = n + 1 := by exact_mod_cast h
          norm_cast; omega
  have hN : N₀ = 2 := by
    have h : ringKrullDim (X.presheaf.stalk y) = N₀ := hz.2
    rw [ringKrullDim_stalk_eq_coheight, hcoh] at h
    exact_mod_cast h.symm
  subst hN
  obtain ⟨a, ha⟩ : ∃ a, jj ⟨Pi, hsupp Pi hPim, hyi⟩ = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, jj ⟨Pj, hsupp Pj hPjm, hyj⟩ = b := ⟨_, rfl⟩
  have hab : a ≠ b := fun h => hPij (congrArg Subtype.val (hjj (ha.trans (h.trans hb.symm))))
  have h2 : ∀ l : Fin 2, l = a ∨ l = b := fun l => by
    have ha := a.isLt
    have hb := b.isLt
    have hl := l.isLt
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rcases (by omega : l.val = a.val ∨ l.val = b.val) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hrange : Set.range ![z a, z b] = Set.range z := by
    ext v
    constructor
    · rintro ⟨l, rfl⟩
      fin_cases l
      · exact ⟨a, rfl⟩
      · exact ⟨b, rfl⟩
    · rintro ⟨l, rfl⟩
      rcases h2 l with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hIa := hI ⟨Pi, hsupp Pi hPim, hyi⟩
  have hIb := hI ⟨Pj, hsupp Pj hPjm, hyj⟩
  rw [ha] at hIa
  rw [hb] at hIb
  refine ⟨z a, z b, ⟨(congrArg Ideal.span hrange).trans hz.1, hz.2⟩, hIa, hIb, fun Γ hΓ hyΓ => ?_⟩
  rcases h2 (jj ⟨Γ, hΓ, hyΓ⟩) with h | h
  · exact Or.inl (congrArg Subtype.val (hjj (h.trans ha.symm)))
  · exact Or.inr (congrArg Subtype.val (hjj (h.trans hb.symm)))

/-- **The residue presentation along one branch.** If a generator `τ` is written as
`ε u (t⁻¹ s⁻¹ dt ∧ ds ∧ dw)^{⊗m}` at `z = ι(νₗ(η_Q))`, with `t, s` a regular system of parameters
and `t` cutting out the floor component `Pₗ`, then the functions `w` and `u` restricted to `T`
present the residue of `τ` along `Tₗ` at `Q` with sign `ε`. -/
private theorem isLogResiduePresentation_branch {n' m : ℕ} (l : N.ι)
    (Q : MMP.Mori.PrimeDivisor (N.X l)) {Pl : MMP.Mori.PrimeDivisor X}
    (hPl : Set.range (N.n l ≫ ι).base = (Pl.support : Set X))
    {τ : RationalPluriForms sX (n' + 2) m} (ρl : RationalPluriForms (N.n l ≫ ι ≫ sX) (n' + 1) m)
    (hρl : IsPoincareResidue sX (N.n l ≫ ι) (n' + 1) m τ ρl)
    (W₀ : X.Opens) (hzW : (N.n l ≫ ι).base Q.genericPoint ∈ W₀) (t₀ s₀ u₀ : Γ(X, W₀))
    (w₀ : Fin n' → Γ(X, W₀)) (ε : ℤ)
    (hzreg : IsRegularSystemOfParameters ![X.presheaf.germ W₀ _ hzW t₀,
      X.presheaf.germ W₀ _ hzW s₀])
    (hIt : AlgebraicGeometry.IdealSheafData.stalk Pl.idealSheaf ((N.n l ≫ ι).base Q.genericPoint) =
      Ideal.span {X.presheaf.germ W₀ _ hzW t₀})
    (hw : letI := stalkAlgebra sX ((N.n l ≫ ι).base Q.genericPoint)
      LinearIndependent (IsLocalRing.ResidueField
        (X.presheaf.stalk ((N.n l ≫ ι).base Q.genericPoint))) fun i =>
        KaehlerDifferential.D k (IsLocalRing.ResidueField
          (X.presheaf.stalk ((N.n l ≫ ι).base Q.genericPoint)))
          (IsLocalRing.residue _ (X.presheaf.germ W₀ _ hzW (w₀ i))))
    (hot : X.ord (algebraMap _ X.functionField (X.presheaf.germ W₀ _ hzW t₀))
      Pl.genericPoint = 1)
    (hos : X.ord (algebraMap _ X.functionField (X.presheaf.germ W₀ _ hzW s₀))
      Pl.genericPoint = 0)
    (hs0 : algebraMap _ X.functionField (X.presheaf.germ W₀ _ hzW s₀) ≠ 0)
    (hτ : letI := functionFieldAlgebra sX
      τ = (algebraMap _ X.functionField ((ε : X.presheaf.stalk _) * X.presheaf.germ W₀ _ hzW u₀) •
        PiTensorProduct.tprod X.functionField
        (fun _ : Fin m => (algebraMap _ X.functionField (X.presheaf.germ W₀ _ hzW t₀))⁻¹ •
          (algebraMap _ X.functionField (X.presheaf.germ W₀ _ hzW s₀))⁻¹ •
          exteriorPower.ιMulti X.functionField (n' + 2) (Fin.cons
            (KaehlerDifferential.D k X.functionField
              (algebraMap _ X.functionField (X.presheaf.germ W₀ _ hzW t₀)))
            (Fin.cons (KaehlerDifferential.D k X.functionField
              (algebraMap _ X.functionField (X.presheaf.germ W₀ _ hzW s₀)))
              fun i => KaehlerDifferential.D k X.functionField
                (algebraMap _ X.functionField (X.presheaf.germ W₀ _ hzW (w₀ i)))))) :
        RationalPluriForms sX (n' + 2) m)) :
    IsLogResiduePresentation N (n' + 1) m l Q (ι ⁻¹ᵁ W₀) hzW (fun i => ι.app W₀ (w₀ i))
      (ι.app W₀ u₀) ε ρl := by
  classical
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : IsClosedImmersion (N.n l ≫ ι) := (hΘ l).2.choose_spec.2.2.1
  letI := functionFieldAlgebra sX
  have hgen : (N.n l ≫ ι) (genericPoint (N.X l)) = Pl.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq (N.n l ≫ ι) Pl hPl
  have hsp : (N.n l ≫ ι) (genericPoint (N.X l)) ⤳ (N.n l ≫ ι) Q.genericPoint :=
    (genericPoint_specializes _).map (N.n l ≫ ι).base.hom.continuous
  have ht : X.ord (algebraMap _ X.functionField (X.presheaf.germ W₀ _ hzW t₀))
      ((N.n l ≫ ι) (genericPoint (N.X l))) = 1 := by rw [hgen]; exact hot
  have hs : IsUnit ((X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ W₀ _ hzW s₀)) := by
    obtain ⟨a, ha, ha'⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
      ((N.n l ≫ ι) (genericPoint (N.X l))) hs0 fun Γ hΓ => by
        rw [hgen] at hΓ
        rw [MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hΓ]
        exact hos
    have : (X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ W₀ _ hzW s₀) = a :=
      IsFractionRing.injective _ X.functionField
        (by rw [MMP.Mori.algebraMap_stalkSpecializes, ha'])
    rw [this]; exact ha
  have hres := isPoincareResidue_of_eq_frame (N.n l ≫ ι) hsp _ _ (fun i => X.presheaf.germ W₀ _
    hzW (w₀ i)) _ ht hs τ hτ
  have hρeq := IsPoincareResidue.unique (hΘ l) hρl hres
  -- the uniformizer along `Q`
  have hker : RingHom.ker ((N.n l ≫ ι).stalkMap Q.genericPoint).hom =
      Ideal.span {X.presheaf.germ W₀ _ hzW t₀} := by
    rw [MMP.Resolution.Internal.TupleRestrictionLift.ker_stalkMap_eq_stalk_ker,
      ker_eq_idealSheaf (N.n l ≫ ι) Pl hPl, hIt]
  have hz := ord_stalkMap_eq_one (N.n l ≫ ι) Q hzreg hker
  letI := functionFieldAlgebra (N.n l ≫ ι ≫ sX)
  have hco : algebraMap ((N.X l).presheaf.stalk Q.genericPoint) (N.X l).functionField
      (((N.n l ≫ ι).stalkMap Q.genericPoint).hom (X.presheaf.germ W₀ _ hzW s₀)) =
      ((N.n l ≫ ι).stalkMap (genericPoint (N.X l))).hom
        ((X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ W₀ _ hzW s₀)) :=
    (Scheme.Hom.stalkSpecializes_stalkMap_apply (N.n l ≫ ι) _ _
      (genericPoint_specializes Q.genericPoint) _).symm
  rw [hco] at hz
  -- the differentials of the coordinates on the residue field of `Q`
  letI := stalkAlgebra sX ((N.n l ≫ ι).base Q.genericPoint)
  letI : Algebra k ((N.X l).residueField Q.genericPoint) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (N.n l ≫ ι ≫ sX).appTop ≫
      (N.X l).Γevaluation Q.genericPoint).hom.toAlgebra
  obtain ⟨e, he, hek⟩ := exists_residueField_ringEquiv sX (N.n l ≫ ι) Q.genericPoint
    (N.n l ≫ ι ≫ sX) (Category.assoc _ _ _).symm
  have hw' := linearIndependent_D_ringEquiv e hek hw
  simp only [he] at hw'
  refine isLogResiduePresentation_of_eq ι N l Q (ι ⁻¹ᵁ W₀) hzW _ _ ε hsp _ _ _ hs ρl hρeq hz
    (fun i => ?_) ?_ hw'
  · rw [Scheme.Hom.germ_stalkMap_apply]; rfl
  · rw [Scheme.Hom.germ_stalkMap_apply]; rfl

/-- **Opposite residues at a double point.** The residues along the two branches `P ⊆ Tᵢ`,
`P' ⊆ Tⱼ` over a double point of `T` in `W` of a generator `τ` of `𝒪_X(m(K_X + B))` on `W` are
presented by the same functions `a`, `g` on `T` with signs `1` and `(-1)^m`. -/
private theorem exists_isLogResiduePresentation_pair {m : ℕ} (hm : 0 < m)
    {W : X.Opens} {τ : RationalPluriForms sX (n + 1) m} (hτ : GeneratesOn B m W τ)
    (ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m)
    (hρ : ∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
      IsPoincareResidue sX (N.n i ≫ ι) n m τ (ρ i))
    (i j : N.ι) (hij : j ≠ i) (P : MMP.Mori.PrimeDivisor (N.X i))
    (P' : MMP.Mori.PrimeDivisor (N.X j))
    (hPP' : (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint)
    (hW : (N.n i).base P.genericPoint ∈ ι ⁻¹ᵁ W) :
    ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
      (hP' : (N.n j).base P'.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V)) (g : Γ(T, V)),
      IsLogResiduePresentation N n m i P V hP a g 1 (ρ i) ∧
        IsLogResiduePresentation N n m j P' V hP' a g ((-1) ^ m) (ρ j) := by
  classical
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  obtain ⟨Pr, hPr, hPm, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have hQr : (N.n i).base P.genericPoint ∈ Set.range (N.n j).base := ⟨P'.genericPoint, hPP'.symm⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
    obtain ⟨x, y', hz, -⟩ := exists_coordinates_of_mem_range ι hdim hK hproj hQ hB
      hdlt hB0 hT N Θ hΘ huniq i j hij P hQr (hPr i) (hPr j) (fun h => hij (hPinj h).symm)
      (hPm i) (hPm j)
    have := (exists_basis_D_cons (sX := sX) hdim _ hz).1
    exact ⟨n - 1, by omega⟩
  obtain ⟨x, y', hz, hIx, hIy, hcomp⟩ := exists_coordinates_of_mem_range ι hdim hK hproj hQ hB
    hdlt hB0 hT N Θ hΘ huniq i j hij P hQr (hPr i) (hPr j) (fun h => hij (hPinj h).symm)
    (hPm i) (hPm j)
  obtain ⟨-, w, hw, b, hb⟩ := exists_basis_D_cons (sX := sX) hdim _ hz
  let y := ι.base ((N.n i).base P.genericPoint)
  letI := stalkAlgebra sX y
  letI := functionFieldAlgebra sX
  -- the frame at `y`
  have hσ : Submodule.span (X.presheaf.stalk y) {(exteriorPower.ιMulti (X.presheaf.stalk y) (n' + 2)
      (fun l => KaehlerDifferential.D k (X.presheaf.stalk y)
        ((Fin.cons x (Fin.cons y' w) : Fin (n' + 2) → X.presheaf.stalk y) l)))} = ⊤ := by
    have h := span_ιMulti_cons_eq_top b (KaehlerDifferential.D k _ x)
      (KaehlerDifferential.D k _ y') (fun l => KaehlerDifferential.D k _ (w l))
      (by rw [hb]; congr 1; funext l; fin_cases l <;> rfl)
    have hfun : (fun l => KaehlerDifferential.D k (X.presheaf.stalk y)
        ((Fin.cons x (Fin.cons y' w) : Fin (n' + 2) → X.presheaf.stalk y) l)) =
        Fin.cons (KaehlerDifferential.D k _ x) (Fin.cons (KaehlerDifferential.D k _ y')
          fun l => KaehlerDifferential.D k _ (w l)) := by
      funext l
      refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun l => ?_) l) l <;> rfl
    rw [hfun]
    exact h
  have hyi : y ∈ (Pr i).support := by rw [← hPr i]; exact ⟨P.genericPoint, rfl⟩
  have hyj : y ∈ (Pr j).support := by
    rw [← hPr j]; exact ⟨P'.genericPoint, by rw [Scheme.Hom.comp_base, TopCat.comp_app, ← hPP']⟩
  have hox : ∀ Γ : MMP.Mori.PrimeDivisor X, y ∈ Γ.support →
      X.ord (algebraMap _ X.functionField x) Γ.genericPoint = if Γ = Pr i then 1 else 0 :=
    fun Γ hΓ => ord_algebraMap_eq_ite_of_stalk_eq_span hz 0 (Pr i) hyi hIx Γ hΓ
  have hoy : ∀ Γ : MMP.Mori.PrimeDivisor X, y ∈ Γ.support →
      X.ord (algebraMap _ X.functionField y') Γ.genericPoint = if Γ = Pr j then 1 else 0 :=
    fun Γ hΓ => ord_algebraMap_eq_ite_of_stalk_eq_span hz 1 (Pr j) hyj hIy Γ hΓ
  have hc1 := fun l => coeff_eq_one_of_mem_roundDown_support hB.nonneg hdlt.2.1 (hPm l)
  have hsupp : ∀ l, Pr l ∈ B.support := fun l => by
    rw [Finsupp.mem_support_iff]; change B.coeff (Pr l) ≠ 0; rw [hc1 l]; exact one_ne_zero
  have hPij : Pr i ≠ Pr j := fun h => hij (hPinj h).symm
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, y ∈ Γ.support →
      Γ.ordForm τ = -(m : ℤ) * (X.ord (algebraMap _ X.functionField x) Γ.genericPoint +
        X.ord (algebraMap _ X.functionField y') Γ.genericPoint) := by
    intro Γ hΓ
    have h := hτ.2 Γ ⟨y, hΓ, hW⟩
    rw [hox Γ hΓ, hoy Γ hΓ]
    have hBΓ : B.coeff Γ = (if Γ = Pr i then 1 else 0) + (if Γ = Pr j then 1 else 0) := by
      by_cases hΓs : Γ ∈ B.support
      · rcases hcomp Γ hΓs hΓ with rfl | rfl
        · rw [if_pos rfl, if_neg hPij, hc1 i]; norm_num
        · rw [if_neg (Ne.symm hPij), if_pos rfl, hc1 j]; norm_num
      · have h0 : B.coeff Γ = 0 := Finsupp.notMem_support_iff.mp hΓs
        have hi' : Γ ≠ Pr i := fun h => hΓs (h ▸ hsupp i)
        have hj' : Γ ≠ Pr j := fun h => hΓs (h ▸ hsupp j)
        rw [h0, if_neg hi', if_neg hj']; norm_num
    rw [hBΓ] at h
    have : ((Γ.ordForm τ : ℤ) : ℚ) = ((-(m : ℤ) * ((if Γ = Pr i then 1 else 0) +
        (if Γ = Pr j then 1 else 0)) : ℤ) : ℚ) := by
      push_cast
      split_ifs at h ⊢ <;> push_cast at h ⊢ <;> linarith
    exact_mod_cast this
  have hx0 : algebraMap (X.presheaf.stalk y) X.functionField x ≠ 0 := fun h => by
    have := hox (Pr i) hyi; rw [h, Scheme.ord_zero, if_pos rfl] at this; exact zero_ne_one this
  have hy0 : algebraMap (X.presheaf.stalk y) X.functionField y' ≠ 0 := fun h => by
    have := hoy (Pr j) hyj; rw [h, Scheme.ord_zero, if_pos rfl] at this; exact zero_ne_one this
  have hdim' : topologicalKrullDim X = ((n' + 2 : ℕ) : WithBot ℕ∞) := hdim
  obtain ⟨u, hu, hτu⟩ :=
    exists_isUnit_eq_smul_tprod hdim' y _ x y' hσ τ hτ.1 hx0 hy0 hord
  -- sections representing the coordinates near `y`
  obtain ⟨Ux, hyUx, x₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf x
  obtain ⟨Uy, hyUy, y₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf y'
  obtain ⟨Uu, hyUu, u₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf u
  choose Uw hyUw w₀ hw₀ using fun l => TopCat.Presheaf.exists_germ_eq X.presheaf (w l)
  let W₀ : X.Opens := Ux ⊓ Uy ⊓ Uu ⊓
    ⟨⋂ l, (Uw l : Set X), isOpen_iInter_of_finite fun l => (Uw l).isOpen⟩
  have hyW₀ : y ∈ W₀ := ⟨⟨⟨hyUx, hyUy⟩, hyUu⟩, Set.mem_iInter.mpr hyUw⟩
  have hWx : W₀ ≤ Ux := fun z hz => hz.1.1.1
  have hWy : W₀ ≤ Uy := fun z hz => hz.1.1.2
  have hWu : W₀ ≤ Uu := fun z hz => hz.1.2
  have hWw : ∀ l, W₀ ≤ Uw l := fun l z hz => Set.mem_iInter.mp hz.2 l
  let x₁ := X.presheaf.map (homOfLE hWx).op x₀
  let y₁ := X.presheaf.map (homOfLE hWy).op y₀
  let u₁ := X.presheaf.map (homOfLE hWu).op u₀
  let w₁ := fun l => X.presheaf.map (homOfLE (hWw l)).op (w₀ l)
  have gx : X.presheaf.germ W₀ y hyW₀ x₁ = X.presheaf.germ Ux y hyUx x₀ :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gy : X.presheaf.germ W₀ y hyW₀ y₁ = X.presheaf.germ Uy y hyUy y₀ :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gu : X.presheaf.germ W₀ y hyW₀ u₁ = X.presheaf.germ Uu y hyUu u₀ :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gw : ∀ l, X.presheaf.germ W₀ y hyW₀ (w₁ l) = w l := fun l =>
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans (hw₀ l)
  -- the frame equation, in a form for each branch
  have hfr : ∀ (a b : X.functionField) (v : Fin n' → Ω[X.functionField⁄k]),
      exteriorPower.ιMulti X.functionField (n' + 2)
        (fun l => KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField
          ((Fin.cons (X.presheaf.germ Ux y hyUx x₀) (Fin.cons (X.presheaf.germ Uy y hyUy y₀) w) :
            Fin (n' + 2) → X.presheaf.stalk y) l))) =
      exteriorPower.ιMulti X.functionField (n' + 2) (Fin.cons
        (KaehlerDifferential.D k X.functionField
          (algebraMap _ X.functionField (X.presheaf.germ W₀ y hyW₀ x₁)))
        (Fin.cons (KaehlerDifferential.D k X.functionField
          (algebraMap _ X.functionField (X.presheaf.germ W₀ y hyW₀ y₁)))
          fun l => KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField (X.presheaf.germ W₀ y hyW₀ (w₁ l))))) := by
    intro _ _ _
    congr 1
    funext l
    refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun l => ?_) l) l
    · simp only [Fin.cons_zero, gx]
    · simp only [Fin.cons_succ, Fin.cons_zero, gy]
    · simp only [Fin.cons_succ, gw]
  have hW'i : ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty := ⟨P.genericPoint, hW⟩
  have hyj' : (N.n j ≫ ι).base P'.genericPoint = y := by
    change ι.base ((N.n j).base P'.genericPoint) = ι.base ((N.n i).base P.genericPoint)
    rw [hPP']
  have hW'j : ((N.n j ≫ ι) ⁻¹ᵁ W : Set (N.X j)).Nonempty := ⟨P'.genericPoint,
    show (N.n j ≫ ι).base P'.genericPoint ∈ W by rw [hyj']; exact hW⟩
  have hzWj : (N.n j ≫ ι).base P'.genericPoint ∈ W₀ := by rw [hyj']; exact hyW₀
  -- the generator in the frame at `y`
  have hτi : τ = (algebraMap _ X.functionField (((1 : ℤ) : X.presheaf.stalk y) *
        X.presheaf.germ W₀ y hyW₀ u₁) •
      PiTensorProduct.tprod X.functionField
      (fun _ : Fin m => (algebraMap _ X.functionField (X.presheaf.germ W₀ y hyW₀ x₁))⁻¹ •
        (algebraMap _ X.functionField (X.presheaf.germ W₀ y hyW₀ y₁))⁻¹ •
        exteriorPower.ιMulti X.functionField (n' + 2) (Fin.cons
          (KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField (X.presheaf.germ W₀ y hyW₀ x₁)))
          (Fin.cons (KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField (X.presheaf.germ W₀ y hyW₀ y₁)))
            fun l => KaehlerDifferential.D k X.functionField
              (algebraMap _ X.functionField (X.presheaf.germ W₀ y hyW₀ (w₁ l)))))) :
      RationalPluriForms sX (n' + 2) m) := by
    rw [← hfr 0 0 (fun _ => 0), Int.cast_one, one_mul, gu, gx, gy]
    exact hτu
  have hPi := isLogResiduePresentation_branch ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i P
    (hPr i) (ρ i) (hρ i hW'i) W₀ hyW₀ x₁ y₁ u₁ w₁ 1
    (by have h := hz; rw [← gx, ← gy] at h; exact h)
    (by have h := hIx; rw [← gx] at h; exact h)
    (by have h := hw; simp only [← gw] at h; exact h)
    (by have h := (hox (Pr i) hyi).trans (if_pos rfl); rw [← gx] at h; exact h)
    (by have h := (hoy (Pr i) hyi).trans (if_neg hPij); rw [← gy] at h; exact h)
    (by have h := hy0; rw [← gy] at h; exact h) hτi
  -- the other branch, at the same point
  have key : ∀ (z : X) (hzz : z ∈ W₀), z = y →
      IsRegularSystemOfParameters ![X.presheaf.germ W₀ z hzz y₁, X.presheaf.germ W₀ z hzz x₁] ∧
      AlgebraicGeometry.IdealSheafData.stalk (Pr j).idealSheaf z =
        Ideal.span {X.presheaf.germ W₀ z hzz y₁} ∧
      (letI := stalkAlgebra sX z;
        LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk z)) fun l =>
          KaehlerDifferential.D k (IsLocalRing.ResidueField (X.presheaf.stalk z))
            (IsLocalRing.residue _ (X.presheaf.germ W₀ z hzz (w₁ l)))) ∧
      X.ord (algebraMap _ X.functionField (X.presheaf.germ W₀ z hzz y₁)) (Pr j).genericPoint = 1 ∧
      X.ord (algebraMap _ X.functionField (X.presheaf.germ W₀ z hzz x₁)) (Pr j).genericPoint = 0 ∧
      algebraMap _ X.functionField (X.presheaf.germ W₀ z hzz x₁) ≠ 0 ∧
      τ = (algebraMap _ X.functionField ((((-1) ^ m : ℤ)) * X.presheaf.germ W₀ z hzz u₁) •
        PiTensorProduct.tprod X.functionField
        (fun _ : Fin m => (algebraMap _ X.functionField (X.presheaf.germ W₀ z hzz y₁))⁻¹ •
          (algebraMap _ X.functionField (X.presheaf.germ W₀ z hzz x₁))⁻¹ •
          exteriorPower.ιMulti X.functionField (n' + 2) (Fin.cons
            (KaehlerDifferential.D k X.functionField
              (algebraMap _ X.functionField (X.presheaf.germ W₀ z hzz y₁)))
            (Fin.cons (KaehlerDifferential.D k X.functionField
              (algebraMap _ X.functionField (X.presheaf.germ W₀ z hzz x₁)))
              fun l => KaehlerDifferential.D k X.functionField
                (algebraMap _ X.functionField (X.presheaf.germ W₀ z hzz (w₁ l)))))) :
        RationalPluriForms sX (n' + 2) m) := by
    rintro z hzz rfl
    refine ⟨?_, by rw [gy]; exact hIy, by simp only [gw]; exact hw,
      by rw [gy]; exact (hoy (Pr j) hyj).trans (if_pos rfl),
      by rw [gx]; exact (hox (Pr j) hyj).trans (if_neg (Ne.symm hPij)),
      by rw [gx]; exact hx0, ?_⟩
    · refine ⟨?_, hz.2⟩
      rw [gx, gy, ← hz.1]
      congr 1
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons,
        Matrix.range_empty, Set.union_empty, Set.union_empty, Set.singleton_union,
        Set.singleton_union, Set.pair_comm]
    · rw [hτi, ιMulti_cons_cons_swap]
      have e : ∀ (a b : X.functionField)
          (F : ⋀[X.functionField]^(n' + 2) Ω[X.functionField⁄k]),
          a • b • (-F) = (-1 : X.functionField) • (b • a • F) := fun a b F => by
        rw [smul_neg, smul_neg, smul_comm a b, neg_one_smul]
      simp only [e]
      rw [MMP.Mori.tprod_const_smul, smul_smul]
      congr 1
      push_cast
      ring
  obtain ⟨hz2, hI2, hw2, ho2, ho2', hx02, hτ2⟩ := key _ hzWj hyj'
  have hPj := isLogResiduePresentation_branch ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq j P'
    (hPr j) (ρ j) (hρ j hW'j) W₀ hzWj y₁ x₁ u₁ w₁ ((-1) ^ m) hz2 hI2 hw2 ho2 ho2' hx02 hτ2
  exact ⟨ι ⁻¹ᵁ W₀, hyW₀, hzWj, fun l => ι.app W₀ (w₁ l), ι.app W₀ u₁, hPi, hPj⟩

/-- A point of a floor component which has codimension one in `T` has codimension one in the
component. -/
private theorem coheight_eq_one_of_coheight_floorComponent (j : N.ι) (q : N.X j)
    (h : Order.coheight ((N.n j).base q) = 1) : Order.coheight q = 1 := by
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  have hmono : StrictMono (N.n j).base := fun a b hab =>
    MMP.Intersection.lt_of_specializes_of_ne (hab.le.map (N.n j).base.hom.continuous)
      (fun h => hab.ne ((N.n j).isClosedEmbedding.injective h))
  have hle := Order.coheight_le_coheight_apply_of_strictMono _ hmono q
  rw [h] at hle
  have hne : q ≠ genericPoint (N.X j) := by
    rintro rfl
    rw [coheight_genericPoint_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq j]
      at h
    exact zero_ne_one h
  have hge : 1 ≤ Order.coheight q := by
    have hlt : q < genericPoint (N.X j) :=
      MMP.Intersection.lt_of_specializes_of_ne (genericPoint_specializes q) hne
    exact le_add_self.trans (Order.coheight_add_one_le hlt)
  exact le_antisymm hle hge

/-- A prime divisor of a floor component whose generic point lies in the double locus of `T` meets
a second floor component in a prime divisor with the same image. -/
private theorem exists_primeDivisor_of_mem_doubleIntersectionLocus (i : N.ι)
    (P : MMP.Mori.PrimeDivisor (N.X i))
    (hD : (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T)) :
    ∃ j, j ≠ i ∧ ∃ P' : MMP.Mori.PrimeDivisor (N.X j),
      (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint := by
  by_contra hcon
  push Not at hcon
  apply notMem_doubleIntersectionLocus_of_single ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ
    huniq i P.genericPoint _ hD
  rintro j hj ⟨q, hq⟩
  have hcohT : Order.coheight ((N.n j).base q) = 1 := by
    rw [hq]
    exact coheight_floorComponent_primeDivisor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i P
  have h1 := coheight_eq_one_of_coheight_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ
    huniq j q hcohT
  set E : MMP.Mori.PrimeDivisor (N.X j) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne q h1
  have hE : E.genericPoint = q := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine hcon j hj E ?_
  rw [hE, hq]

/-- **Residues at the double locus.** Let `τ` generate `𝒪_X(m(K_X + B))` on `W` and let `ρ` be
its family of Poincaré residues along the floor components meeting `W`. At a point of the double
locus of `T` in `W`, lying on the branches `P ⊆ Tᵢ` and `P' ⊆ Tⱼ`, the residues of `ρᵢ` and `ρⱼ`
are `ḡ (dā)^{⊗m}` and `(-1)^m ḡ (dā)^{⊗m}` for functions `a`, `g` on `T`: in snc coordinates
`x, y` cutting out the two components, `τ = u (dx/x ∧ dy/y ∧ dw)^{⊗m}`, and taking the residue
along `x = 0` or along `y = 0` first differs by the sign of the transposition. -/
private theorem exists_isLogResiduePresentation_floor {m : ℕ} (hm : 0 < m)
    (hC : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    {W : X.Opens} {τ : RationalPluriForms sX (n + 1) m} (hτ : GeneratesOn B m W τ)
    (ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m)
    (hρ : ∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
      IsPoincareResidue sX (N.n i ≫ ι) n m τ (ρ i)) :
    (∀ (i j : N.ι) (P : MMP.Mori.PrimeDivisor (N.X i)) (P' : MMP.Mori.PrimeDivisor (N.X j)),
      (N.n i).base P.genericPoint = (N.n j).base P'.genericPoint →
      (N.n i).base P.genericPoint ∈ ι ⁻¹ᵁ W →
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
      (⟨i, P.genericPoint⟩ : Σ i, N.X i) ≠ ⟨j, P'.genericPoint⟩ →
      ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
        (hP' : (N.n j).base P'.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V)) (g : Γ(T, V)),
        IsLogResiduePresentation N n m i P V hP a g 1 (ρ i) ∧
          IsLogResiduePresentation N n m j P' V hP' a g ((-1) ^ m) (ρ j)) ∧
      ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ ι ⁻¹ᵁ W →
        (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
        ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V))
          (g : Γ(T, V)), IsLogResiduePresentation N n m i P V hP a g 1 (ρ i) := by
  classical
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  have hsecond := exists_primeDivisor_of_mem_doubleIntersectionLocus ι hdim hK hproj hQ hB hdlt
    hB0 hT N Θ hΘ huniq
  refine ⟨fun i j P P' hPP' hW _ hne => ?_, fun i P hW hD => ?_⟩
  · by_cases hij : j = i
    · subst hij
      exact absurd (congrArg (Sigma.mk j) ((N.n j).isClosedEmbedding.injective hPP')) hne
    · exact exists_isLogResiduePresentation_pair ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
        hm hτ ρ hρ i j hij P P' hPP' hW
  · obtain ⟨j, hij, P', hPP'⟩ := hsecond i P hD
    obtain ⟨V, hP, -, a, g, h, -⟩ := exists_isLogResiduePresentation_pair ι hdim hK hproj hQ hB
      hdlt hB0 hT N Θ hΘ huniq hm hτ ρ hρ i j hij P P' hPP' hW
    exact ⟨V, hP, a, g, h⟩

/-- **Residue adjunction along the floor.** The residues of a local generator of the log
canonical sheaf exist on every floor component and form a local adjoint generator. -/
private theorem residueIdentification_floor : ResidueIdentification ι N n K B Θ := by
  classical
  intro m hm hC W τ hτ
  have hres := fun i (hi : ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty) =>
    exists_isPoincareResidue_and_generatesOn ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i hm
      hC hτ hi
  have hex : ∀ i, ∃ ρ : RationalPluriForms (N.n i ≫ ι ≫ sX) n m,
      ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty → IsPoincareResidue sX (N.n i ≫ ι) n m τ ρ := by
    intro i
    by_cases hi : ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty
    · obtain ⟨ρ, hρ⟩ := (hres i hi).1
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose ρ₀ hρ₀ using hex
  refine ⟨⟨ρ₀, hρ₀⟩, fun ρ hρ hρ0 => ⟨fun i => ?_, ?_⟩⟩
  · by_cases hi : ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty
    · exact (hres i hi).2 (ρ i) (hρ i hi)
    · refine ⟨hρ0 i, fun Γ hΓ => absurd ?_ hi⟩
      obtain ⟨z, -, hz⟩ := hΓ
      exact ⟨z, hz⟩
  · exact (exists_isLogResiduePresentation_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq hm
      hC hτ ρ hρ).1

open Classical in
/-- The kernel of `𝒪_{X,ι(t)} → 𝒪_{T,t}` is the intersection of the ideals of the components of
`⌊B⌋` through `ι(t)`. -/
private theorem ker_stalkMap_eq_inf (t : T) :
    RingHom.ker (ι.stalkMap t).hom = (B.roundDown.support.filter
      fun E => ι.base t ∈ E.support).inf fun E => IdealSheafData.stalk E.idealSheaf (ι.base t) := by
  classical
  have hk : ι.ker = MMP.Mori.DivisorWithCoeffs.suppIdeal B.roundDown := by
    rw [ker_eq_vanishingIdeal]
    unfold MMP.Mori.DivisorWithCoeffs.suppIdeal
    congr 1
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_closure, ι.isClosedEmbedding.isClosed_range.closure_eq, hT,
      MMP.Mori.DivisorWithCoeffs.supp, TopologicalSpace.Closeds.coe_finset_sup,
      Finset.sup_set_eq_biUnion]
    rfl
  rw [MMP.Resolution.Internal.TupleRestrictionLift.ker_stalkMap_eq_stalk_ker, hk,
    MMP.Intersection.stalk_suppIdeal]

/-- **The local rings of the floor in codimension at most one are seminormal.** Such a local
ring is a field, a regular local ring, or, at a point of the double locus, `𝒪_{X,y} ⧸ (x) ∩ (y')`
for a regular system of parameters `x, y'` of `𝒪_{X,y}` cutting out the two floor components
through `y`; the latter is seminormal since both branches `𝒪_{X,y} ⧸ (x)` and `𝒪_{X,y} ⧸ (y')` are
regular and meet in the residue field. -/
private theorem isSeminormalRing_stalk_floor (t : T)
    (ht : ¬ 2 ≤ ringKrullDim (T.presheaf.stalk t)) : IsSeminormalRing (T.presheaf.stalk t) := by
  classical
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  by_cases hreg : IsRegularLocalRing (T.presheaf.stalk t)
  · exact isSeminormalRing_of_isRegularLocalRing _
  have hc : Order.coheight t < 1 + 1 := by
    rw [ringKrullDim_stalk_eq_coheight] at ht
    by_contra h
    rw [one_add_one_eq_two] at h
    exact ht (WithBot.coe_le_coe.mpr (not_lt.mp h))
  rcases (Order.le_of_lt_add_one hc).lt_or_eq with h0 | h1
  · -- a generic point: the local ring is a field
    have h0' : Order.coheight t = 0 := ENat.lt_one_iff_eq_zero.mp h0
    have hdim0 : ringKrullDim (T.presheaf.stalk t) = 0 := by
      rw [ringKrullDim_stalk_eq_coheight, h0']; rfl
    haveI : Ring.KrullDimLE 0 (T.presheaf.stalk t) := by
      rw [Ring.krullDimLE_iff, hdim0]; rfl
    letI := (Ring.KrullDimLE.isField_of_isReduced (R := T.presheaf.stalk t)).toField
    exact _root_.isSeminormalRing_of_isIntegrallyClosed _
  -- a point of the double locus
  have hD : t ∈ (doubleIntersectionLocus T : Set T) := subset_closure ⟨h1, hreg⟩
  obtain ⟨i, s, rfl⟩ := exists_mem_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ
    huniq t
  have hs1 := coheight_eq_one_of_coheight_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ
    huniq i s h1
  set Q : MMP.Mori.PrimeDivisor (N.X i) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne s hs1
  have hQs : Q.genericPoint = s := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  rw [← hQs] at hD ⊢
  obtain ⟨j, hij, P', hPP'⟩ := exists_primeDivisor_of_mem_doubleIntersectionLocus ι hdim hK hproj
    hQ hB hdlt hB0 hT N Θ hΘ huniq i Q hD
  obtain ⟨P, hPr, hPmem, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  have hPij : P i ≠ P j := fun h => hij (hPinj h).symm
  obtain ⟨x, y', hz, hIi, hIj, hoth⟩ := exists_coordinates_of_mem_range ι hdim hK hproj hQ hB hdlt
    hB0 hT N Θ hΘ huniq i j hij Q ⟨_, hPP'.symm⟩ (hPr i) (hPr j) hPij (hPmem i) (hPmem j)
  have hsupp : ∀ G ∈ B.roundDown.support, G ∈ B.support := fun _ hG =>
    mem_support_of_mem_roundDown_support hB.nonneg hdlt.2.1 hG
  -- the kernel of `𝒪_{X,y} → 𝒪_{T,t}` is `(x) ∩ (y')`
  have hker : RingHom.ker (ι.stalkMap ((N.n i).base Q.genericPoint)).hom =
      Ideal.span {x} ⊓ Ideal.span {y'} := by
    rw [ker_stalkMap_eq_inf ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq]
    have hF : B.roundDown.support.filter
        (fun E => ι.base ((N.n i).base Q.genericPoint) ∈ E.support) = {P i, P j} := by
      ext E
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hE, hyE⟩
        exact hoth E (hsupp E hE) hyE
      · rintro (rfl | rfl)
        · exact ⟨hPmem i, by rw [← hPr i]; exact ⟨Q.genericPoint, rfl⟩⟩
        · refine ⟨hPmem j, ?_⟩
          rw [← hPr j]
          exact ⟨P'.genericPoint, by rw [Scheme.Hom.comp_base, TopCat.comp_app, ← hPP']⟩
    erw [hF]
    rw [Finset.inf_insert, Finset.inf_singleton, hIi, hIj]
  -- the two branches are regular and meet in the residue field
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hrx, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz {0}
  obtain ⟨hry, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz {1}
  have e0 : Ideal.span (![x, y'] '' (({0} : Finset (Fin 2)) : Set (Fin 2))) = Ideal.span {x} := by
    simp
  have e1 : Ideal.span (![x, y'] '' (({1} : Finset (Fin 2)) : Set (Fin 2))) = Ideal.span {y'} := by
    simp
  rw [e0] at hrx
  rw [e1] at hry
  have hm : Ideal.span {x} ⊔ Ideal.span {y'} =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (ι.base ((N.n i).base Q.genericPoint))) := by
    rw [← hz.1, ← Ideal.span_union]
    congr 1
    ext
    simp [Fin.exists_fin_two, or_comm, eq_comm]
  have hred : IsReduced (X.presheaf.stalk (ι.base ((N.n i).base Q.genericPoint)) ⧸
      (Ideal.span {x} ⊔ Ideal.span {y'})) := by
    rw [hm]
    infer_instance
  have hsn := isSeminormalRing_quotient_inf _ _ (isSeminormalRing_of_isRegularLocalRing _)
    (isSeminormalRing_of_isRegularLocalRing _) hred
  rw [← hker] at hsn
  exact AlgebraicGeometry.seminormalRing_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (ι.stalkMap_surjective _)) hsn

/-- **The floor is seminormal.** Its local rings in codimension at most one are seminormal, and
`T` is `S₂`, so local square and cube roots glue and extend across codimension two. -/
private theorem isSeminormal_floor : IsSeminormal T := by
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian ι
  have hS2 := satisfiesS2_of_isCMScheme (isCMScheme_floor ι hdim hK hproj hQ hB hdlt hB0 hT)
  intro t
  obtain ⟨U, hU, htU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := t) (U := ⊤) trivial
  exact ⟨⟨U, hU⟩, htU, isSeminormalRing_sections_of_satisfiesS2 hS2
    (fun t ht => isSeminormalRing_stalk_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq t ht)
    U⟩

/-- **The floor has double normal crossings in codimension one.** Off the closed set of
non-regular points of `T` lying over the bad set `Z` of the dlt condition or on three floor
components, which has codimension at least two since a point of codimension one of `T` is regular
or a double point over the snc locus, a closed point is regular, hence smooth, or lies on exactly
two floor components meeting in snc coordinates `z_a, z_b`; then `𝒪_{T,x} = 𝒪_{X,x} ⧸ (z_a z_b)`
and its completion is `k[[x₀, …, xₙ]]/(x₀x₁)`. -/
private theorem isNcInCodimOne_floor : IsNcInCodimOne (ι ≫ sX) n := by
  classical
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  have hNF := isNFold_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  refine ⟨hNF, ?_⟩
  obtain ⟨⟨hpair, -, -⟩, -, Z, -, hsnc, hpos⟩ := id hdlt
  haveI hlft : LocallyOfFiniteType sX := hpair.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι ≫ sX) := hNF.1.2.1
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)
  rw [inverseTransformDivisor_ι_eq_restrictOpen] at hsnc
  have hsupp : ∀ G ∈ B.roundDown.support, G ∈ B.support := fun _ hG =>
    mem_support_of_mem_roundDown_support hB.nonneg hdlt.2.1 hG
  -- the points of `X` on three floor components
  let Bad3 : Set X := ⋃ P ∈ B.roundDown.support, ⋃ Q ∈ B.roundDown.support,
    ⋃ R ∈ B.roundDown.support, ⋃ (_ : P ≠ Q) (_ : P ≠ R) (_ : Q ≠ R),
      (P.support : Set X) ∩ Q.support ∩ R.support
  have hBad3 : IsClosed Bad3 := by
    refine isClosed_biUnion_finset fun P _ => isClosed_biUnion_finset fun Q _ =>
      isClosed_biUnion_finset fun R _ => isClosed_iUnion_of_finite fun _ =>
        isClosed_iUnion_of_finite fun _ => isClosed_iUnion_of_finite fun _ => ?_
    exact (P.idealSheaf.support.isClosed.inter Q.idealSheaf.support.isClosed).inter
      R.idealSheaf.support.isClosed
  have hnot3 : ∀ y : X, y ∉ Bad3 → ∀ P ∈ B.roundDown.support, ∀ Q ∈ B.roundDown.support,
      ∀ R ∈ B.roundDown.support, y ∈ P.support → y ∈ Q.support → y ∈ R.support →
        P = Q ∨ P = R ∨ Q = R := by
    intro y hy P hP Q hQ' R hR h1 h2 h3
    by_contra hne
    push Not at hne
    apply hy
    simp only [Bad3, Set.mem_iUnion]
    exact ⟨P, hP, Q, hQ', R, hR, hne.1, hne.2.1, hne.2.2, ⟨h1, h2⟩, h3⟩
  let U : Set T := regularLocus T ∪ ι.base ⁻¹' ((Z : Set X)ᶜ ∩ Bad3ᶜ)
  have hU : IsOpen U := (MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (ι ≫ sX)).union
    ((Z.isClosed.isOpen_compl.inter hBad3.isOpen_compl).preimage ι.base.hom.continuous)
  refine ⟨⟨Uᶜ, hU.isClosed_compl⟩, MMP.Flips.two_le_closedsCodimension_compl hU ?_, ?_⟩
  · -- every point of codimension at most one is regular or a double point over the snc locus
    intro t ht
    by_cases hreg : IsRegularLocalRing (T.presheaf.stalk t)
    · exact Or.inl hreg
    right
    have h1 : Order.coheight t = 1 := by
      rcases ht.lt_or_eq with h0 | h1
      · exact absurd (MMP.Flips.isRegularLocalRing_stalk_of_coheight_eq_zero
          (ENat.lt_one_iff_eq_zero.mp h0)) hreg
      · exact h1
    have hD : t ∈ (doubleIntersectionLocus T : Set T) := subset_closure ⟨h1, hreg⟩
    obtain ⟨i, s, rfl⟩ := exists_mem_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
      hΘ huniq t
    have hs1 := coheight_eq_one_of_coheight_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
      hΘ huniq i s h1
    set Q : MMP.Mori.PrimeDivisor (N.X i) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne s hs1
    have hQs : Q.genericPoint = s := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    rw [← hQs] at hD ⊢
    obtain ⟨j, hij, P', hPP'⟩ := exists_primeDivisor_of_mem_doubleIntersectionLocus ι hdim hK
      hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i Q hD
    obtain ⟨P, hPr, hPmem, hPinj, -⟩ :=
      exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
    have hPij : P i ≠ P j := fun h => hij (hPinj h).symm
    obtain ⟨-, -, -, -, -, hoth⟩ := exists_coordinates_of_mem_range ι hdim hK hproj hQ hB hdlt
      hB0 hT N Θ hΘ huniq i j hij Q ⟨_, hPP'.symm⟩ (hPr i) (hPr j) hPij (hPmem i) (hPmem j)
    refine ⟨notMem_badSet_of_mem_range ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i j hij Q
      ⟨_, hPP'.symm⟩ hpos, fun h3 => ?_⟩
    simp only [Bad3, Set.mem_iUnion] at h3
    obtain ⟨P1, hP1, Q1, hQ1, R1, hR1, h12, h13, h23, ⟨h1', h2'⟩, h3'⟩ := h3
    rcases hoth P1 (hsupp P1 hP1) h1' with rfl | rfl <;>
      rcases hoth Q1 (hsupp Q1 hQ1) h2' with rfl | rfl <;>
      rcases hoth R1 (hsupp R1 hR1) h3' with rfl | rfl <;>
      first | exact h12 rfl | exact h13 rfl | exact h23 rfl
  · intro x hx hxU
    have hxU' : x ∈ U := not_not.mp hxU
    by_cases hreg : IsRegularLocalRing (T.presheaf.stalk x)
    · -- a regular closed point is smooth
      left
      letI := MMP.Mori.stalkAlgebra (ι ≫ sX) x
      haveI := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed (ι ≫ sX) x hx
      have hres := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
        (K := IsLocalRing.ResidueField (T.presheaf.stalk x))).2
      refine MMP.Flips.mem_smoothLocus_of_isRegularLocalRing (ι ≫ sX) x hreg fun a => ?_
      obtain ⟨c, hc⟩ := hres (IsLocalRing.residue _ a)
      refine ⟨c, ?_⟩
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc,
        IsScalarTower.algebraMap_apply k (T.presheaf.stalk x)
          (IsLocalRing.ResidueField (T.presheaf.stalk x)),
        IsLocalRing.ResidueField.algebraMap_eq]
      exact sub_self _
    right
    obtain ⟨hxZ, hx3⟩ := hxU'.resolve_left hreg
    refine ⟨hNF, hx, ?_⟩
    -- snc coordinates at `ι x`
    let U' : X.Opens := Z.compl
    have hyU : ι.base x ∈ U' := hxZ
    obtain ⟨N₀, z₀, jj, hz₀, hjj, hI⟩ :=
      (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U'.ι B ⟨_, hyU⟩).mp
        (hsnc.2 ⟨_, hyU⟩)
    obtain ⟨z, hzz⟩ : ∃ z : Fin N₀ → X.presheaf.stalk (ι.base x), z = z₀ := ⟨z₀, rfl⟩
    have hz : MMP.Mori.IsRegularSystemOfParameters z := by subst hzz; exact hz₀
    have hcl : IsClosed ({ι.base x} : Set X) := by
      have := ι.isClosedEmbedding.isClosedMap _ hx
      rwa [Set.image_singleton] at this
    have hN : N₀ = n + 1 := by
      have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (ι.base x)
      have h0 : topologicalKrullDim ({ι.base x} : Set X) = 0 := by
        haveI : Subsingleton ({ι.base x} : Set X) := Set.subsingleton_singleton.coe_sort
        haveI : Nonempty ({ι.base x} : Set X) := ⟨⟨_, rfl⟩⟩
        exact AlgebraicGeometry.topologicalKrullDim_eq_zero_of_subsingleton
      rw [hcl.closure_eq, h0, zero_add, hdim] at h
      have h2 : ringKrullDim (X.presheaf.stalk (ι.base x)) = N₀ := hz.2
      rw [ringKrullDim_stalk_eq_coheight, h] at h2
      exact_mod_cast h2.symm
    subst hN
    haveI := isRegularLocalRing_of_isRegularSystemOfParameters hz
    -- the floor components through `ι x`
    obtain ⟨P, hP, hyP⟩ : ∃ P ∈ B.roundDown.support, ι.base x ∈ P.support := by
      have : ι.base x ∈ Set.range ι.base := ⟨x, rfl⟩
      rw [hT] at this
      simpa using this
    have hker := ker_stalkMap_eq_inf ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq x
    by_cases hQ' : ∃ Q ∈ B.roundDown.support, Q ≠ P ∧ ι.base x ∈ Q.support
    · obtain ⟨Q, hQm, hQP, hyQ⟩ := hQ'
      have hF : B.roundDown.support.filter (fun E => ι.base x ∈ E.support) = {P, Q} := by
        ext E
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hE, hyE⟩
          rcases hnot3 _ hx3 P hP Q hQm E hE hyP hyQ hyE with h | h | h
          · exact absurd h.symm hQP
          · exact Or.inl h.symm
          · exact Or.inr h.symm
        · rintro (rfl | rfl)
          · exact ⟨hP, hyP⟩
          · exact ⟨hQm, hyQ⟩
      have hab : jj ⟨P, hsupp P hP, hyP⟩ ≠ jj ⟨Q, hsupp Q hQm, hyQ⟩ := fun h =>
        hQP (congrArg Subtype.val (hjj h)).symm
      have hIP : IdealSheafData.stalk P.idealSheaf (ι.base x) =
          Ideal.span {z (jj ⟨P, hsupp P hP, hyP⟩)} := by subst hzz; exact hI ⟨P, hsupp P hP, hyP⟩
      have hIQ : IdealSheafData.stalk Q.idealSheaf (ι.base x) =
          Ideal.span {z (jj ⟨Q, hsupp Q hQm, hyQ⟩)} := by
        subst hzz; exact hI ⟨Q, hsupp Q hQm, hyQ⟩
      rw [hF, Finset.inf_insert, Finset.inf_singleton, hIP, hIQ,
        span_inf_span_eq_span_mul hz hab] at hker
      exact hasCompletedLocalModel_of_ker_eq_span_mul sX ι hx hz hab hker
    · -- on one component `T` is regular at `x`
      push Not at hQ'
      have hF : B.roundDown.support.filter (fun E => ι.base x ∈ E.support) = {P} := by
        ext E
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hE, hyE⟩
          by_contra hEP
          exact hQ' E hE hEP hyE
        · rintro rfl
          exact ⟨hP, hyP⟩
      have hIP : IdealSheafData.stalk P.idealSheaf (ι.base x) =
          Ideal.span {z (jj ⟨P, hsupp P hP, hyP⟩)} := by subst hzz; exact hI ⟨P, hsupp P hP, hyP⟩
      rw [hF, Finset.inf_singleton, hIP] at hker
      exfalso
      apply hreg
      have hr :=
        MMP.Resolution.isRegularLocalRing_quotient_span_singleton_of_isRegularSystemOfParameters
          hz (jj ⟨P, hsupp P hP, hyP⟩)
      rw [← hker] at hr
      exact IsRegularLocalRing.of_ringEquiv
        (RingHom.quotientKerEquivOfSurjective (ι.stalkMap_surjective x))

/-- **The boundary of the floor.** The differents `Θᵢ` define a rational boundary `Δ` on `T`
away from the double locus, with `Θᵢ = Cᵢ + Δᵢ`. -/
private theorem exists_isAdjointBoundary :
    ∃ Δ : QWeilDivisor T, Δ.IsBoundary (ι ≫ sX) ∧
      (∀ Γ ∈ Δ.support, Γ.1.genericPoint ∉ (doubleIntersectionLocus T : Set T)) ∧
      ∀ i, IsAdjointBoundary N Δ i (Θ i) := by
  classical
  obtain ⟨P, -, hPmem, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : Finite N.ι := Finite.of_injective
    (fun i => (⟨P i, hPmem i⟩ : {Q // Q ∈ B.roundDown.support}))
    fun a b h => hPinj (congrArg Subtype.val h)
  haveI : Fintype N.ι := Fintype.ofFinite _
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  -- branches over a point on a single component
  let single : (Σ i, MMP.Mori.PrimeDivisor (N.X i)) → Prop := fun x =>
    ∀ j, j ≠ x.1 → (N.n x.1).base x.2.genericPoint ∉ Set.range (N.n j).base
  have hΓ : ∀ x, single x → ∃ Γ : WeilDivisorPrime T,
      Γ.1.genericPoint = (N.n x.1).base x.2.genericPoint := by
    rintro ⟨i, Q⟩ hx
    have h1 := coheight_floorComponent_primeDivisor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ
      huniq i Q
    set E : MMP.Mori.PrimeDivisor T := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
    have hE : E.genericPoint = (N.n i).base Q.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have hreg := isRegularLocalRing_stalk_of_single ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ
      huniq i Q.genericPoint Q.coheight_genericPoint hx
    have hdvr : ∃ _ : IsDomain E.localRing, IsDiscreteValuationRing E.localRing := by
      change ∃ _ : IsDomain (T.presheaf.stalk E.genericPoint),
        IsDiscreteValuationRing (T.presheaf.stalk E.genericPoint)
      rw [hE]
      exact MMP.Resolution.Kollar.isDiscreteValuationRing_of_ringKrullDim_eq_one
        (by rw [ringKrullDim_stalk_eq_coheight, h1]; rfl)
    exact ⟨⟨E, hdvr⟩, hE⟩
  choose Γ hΓgen using hΓ
  have hΓeq : ∀ x (hx : single x) (G : WeilDivisorPrime T),
      G.1.genericPoint = (N.n x.1).base x.2.genericPoint → G = Γ x hx := fun x hx G hG =>
    Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hG.trans (hΓgen x hx).symm))
  have hΓinj : ∀ x (hx : single x) y (hy : single y), Γ x hx = Γ y hy → x = y := by
    rintro ⟨i, Q⟩ hx ⟨i', Q'⟩ hy h
    have hg := (hΓgen _ hx).symm.trans ((congrArg (fun G : WeilDivisorPrime T => G.1.genericPoint)
      h).trans (hΓgen _ hy))
    by_cases hii : i' = i
    · subst hii
      exact congrArg (Sigma.mk i') (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((N.n i').isClosedEmbedding.injective hg))
    · exact absurd ⟨Q'.genericPoint, hg.symm⟩ (hx i' hii)
  let S : Finset (Σ i, MMP.Mori.PrimeDivisor (N.X i)) :=
    (Finset.univ.sigma fun i => (Θ i).support).filter single
  let Δ : QWeilDivisor T := ∑ x ∈ S.attach,
    Finsupp.single (Γ x.1 (Finset.mem_filter.mp x.2).2) ((Θ x.1.1).coeff x.1.2)
  have hΔapp : ∀ G : WeilDivisorPrime T, Δ G = ∑ x ∈ S.attach,
      if Γ x.1 (Finset.mem_filter.mp x.2).2 = G then (Θ x.1.1).coeff x.1.2 else 0 := by
    intro G
    simp only [Δ, Finsupp.finset_sum_apply, Finsupp.single_apply]
  -- the value of `Δ` at a branch prime
  have hΔΓ : ∀ x (hx : single x), Δ (Γ x hx) = (Θ x.1).coeff x.2 := by
    intro x hx
    rw [hΔapp]
    by_cases hxS : x ∈ S
    · rw [Finset.sum_eq_single ⟨x, hxS⟩]
      · simp
      · rintro ⟨y, hyS⟩ - hyx
        rw [if_neg]
        intro h
        exact hyx (Subtype.ext (hΓinj _ _ _ _ h))
      · intro h; exact absurd (Finset.mem_attach _ _) h
    · have h0 : (Θ x.1).coeff x.2 = 0 := by
        by_contra h
        exact hxS (Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
          Finsupp.mem_support_iff.mpr h⟩, hx⟩)
      rw [h0]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg]
      intro h
      exact hxS (hΓinj _ _ _ _ h ▸ y.2)
  -- `Δ` vanishes away from the branch primes
  have hΔzero : ∀ G : WeilDivisorPrime T, (∀ x (hx : single x), Γ x hx ≠ G) → Δ G = 0 :=
    fun G hG => by
      rw [hΔapp]
      exact Finset.sum_eq_zero fun y _ => if_neg (hG _ _)
  have hsupp : ∀ G ∈ Δ.support, ∃ x, ∃ hx : single x, Γ x hx = G := fun G hG => by
    by_contra h
    push Not at h
    exact Finsupp.mem_support_iff.mp hG (hΔzero G h)
  have hdl := isDltPair_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  have hsuppD : ∀ G ∈ Δ.support, G.1.genericPoint ∉ (doubleIntersectionLocus T : Set T) :=
    fun G hG => by
      obtain ⟨x, hx, rfl⟩ := hsupp G hG
      rw [hΓgen]
      exact notMem_doubleIntersectionLocus_of_single ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ
        huniq x.1 x.2.genericPoint hx
  refine ⟨Δ, ⟨(isNFold_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq).1, inferInstance,
    satisfiesS2_of_isCMScheme (isCMScheme_floor ι hdim hK hproj hQ hB hdlt hB0 hT),
    fun G => ?_⟩, hsuppD, fun i Q => ?_⟩
  · by_cases h : ∃ x, ∃ hx : single x, Γ x hx = G
    · obtain ⟨x, hx, rfl⟩ := h
      rw [hΔΓ]
      exact ⟨(hdl x.1).1.2.1 x.2, (hdl x.1).2.1 x.2⟩
    · push Not at h
      rw [hΔzero G h]
      exact ⟨le_rfl, zero_le_one⟩
  · unfold adjointBoundaryCoeff
    by_cases hx : single ⟨i, Q⟩
    · rw [if_neg (notMem_doubleIntersectionLocus_of_single ι hdim hK hproj hQ hB hdlt hB0 hT N
        Θ hΘ huniq i Q.genericPoint hx), zero_add]
      by_cases hmem : Γ ⟨i, Q⟩ hx ∈ Δ.support
      · rw [Finset.sum_eq_single (Γ ⟨i, Q⟩ hx)]
        · rw [if_pos (hΓgen _ hx).symm, hΔΓ]
        · intro G hG hne
          rw [if_neg]
          intro h
          exact hne (hΓeq _ hx G h.symm)
        · intro h; exact absurd hmem h
      · have h0 : Δ (Γ ⟨i, Q⟩ hx) = 0 := Finsupp.notMem_support_iff.mp hmem
        rw [hΔΓ] at h0
        rw [h0]
        refine (Finset.sum_eq_zero fun G hG => ?_).symm
        rw [if_neg]
        intro h
        exact hmem (hΓeq _ hx G h.symm ▸ hG)
    · simp only [single, not_forall, not_not] at hx
      obtain ⟨j, hj, hjr⟩ := hx
      rw [if_pos (mem_doubleIntersectionLocus_of_mem_range ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
        hΘ huniq i j hj Q hjr), coeff_eq_one_of_mem_range ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
        hΘ huniq i j hj Q hjr]
      rw [Finset.sum_eq_zero, add_zero]
      intro G hG
      rw [if_neg]
      intro h
      exact hsuppD G hG (h ▸ mem_doubleIntersectionLocus_of_mem_range ι hdim hK hproj hQ hB hdlt
        hB0 hT N Θ hΘ huniq i j hj Q hjr)

/-- **Dlt adjunction to a floor component.** Each `(Tᵢ, Θᵢ)` is a dlt pair for some canonical
divisor `K` of `Tᵢ`. -/
private theorem exists_isDltPair_floorComponent (i : N.ι) :
    ∃ K : Divisor (N.X i), IsDltPair (N.n i ≫ ι ≫ sX) n K (Θ i) := by
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  have hd' := isDltPair_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i
  obtain ⟨-, n', K', hK', -⟩ := hd'.1.1
  obtain rfl : n' = n := by
    have h := hK'.topologicalKrullDim_eq
    rw [topologicalKrullDim_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i] at h
    exact_mod_cast h.symm
  exact ⟨K', (MMP.Threefold.Bridges.isDltPair_iff_isDltPair _ hK' _).mp hd'⟩

/-- **The adjoint of the floor is `ℚ`-invertible.** A Cartier multiple `m(K_X + B)` has local
generators near every point of `T`, and their residues are local generators of the `m`-th
adjoint sheaf, with residues along the conductor pulled back from `T`. -/
private theorem exists_isAdjointGeneratorOn_floor (Δ : QWeilDivisor T)
    (hΔ : ∀ i, IsAdjointBoundary N Δ i (Θ i)) :
    ∃ m : ℕ, 0 < m ∧ (∀ Γ, ((m : ℚ) * Δ Γ).den = 1) ∧
      ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (s : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m),
        IsAdjointGeneratorOn N n m Θ U s ∧
          ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
            (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
            ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
              (a : Fin (n - 1) → Γ(T, V)) (g : Γ(T, V)),
              IsLogResiduePresentation N n m i P V hP a g 1 (s i) := by
  classical
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  have hXv : IsNormalVariety k sX := hB.isPair.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : CompactSpace X := haveI := hXv.1; QuasiCompact.compactSpace_of_compactSpace sX
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  -- a Cartier multiple of `K_X + B`
  obtain ⟨-, n', K', hK', hQ'⟩ := hB.isPair
  have hQK : (Divisor.toQDivisor K + B).IsQCartier :=
    hQ'.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXv hK' hK)
  obtain ⟨m, hm, hmC⟩ := hQK.exists_pos
  have hpair : MMP.Mori.IsPair sX B := ⟨hXv, n + 1, K, hK, hQK⟩
  have hRI := residueIdentification_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  -- residues of local generators
  have hloc : ∀ y : X, ∃ (W : X.Opens) (_ : y ∈ W) (τ : RationalPluriForms sX (n + 1) m),
      GeneratesOn B m W τ ∧ ∃ s : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m,
      IsAdjointGeneratorOn N n m Θ (ι ⁻¹ᵁ W) s ∧
      ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ ι ⁻¹ᵁ W →
        (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
        ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V))
          (g : Γ(T, V)), IsLogResiduePresentation N n m i P V hP a g 1 (s i) := by
    intro y
    obtain ⟨-, W, hyW, τ, hτ⟩ := MMP.Positivity.IsPair.exists_generatesOn hpair hK hmC y
    have hres := fun i (hi : ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty) =>
      exists_isPoincareResidue_and_generatesOn ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i hm
        hmC hτ hi
    have hex : ∀ i, ∃ σ : RationalPluriForms (N.n i ≫ ι ≫ sX) n m, σ ≠ 0 ∧
        (((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
          IsPoincareResidue sX (N.n i ≫ ι) n m τ σ) := by
      intro i
      by_cases hi : ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty
      · obtain ⟨σ, hσ⟩ := (hres i hi).1
        exact ⟨σ, ((hres i hi).2 σ hσ).1, fun _ => hσ⟩
      · haveI : LocallyOfFiniteType (N.n i ≫ ι ≫ sX) :=
          (N.isNormalVariety i).1.toLocallyOfFiniteType
        letI := functionFieldAlgebra (N.n i ≫ ι ≫ sX)
        obtain ⟨b⟩ := exists_basis_topForms (sX := N.n i ≫ ι ≫ sX) (d := n)
          (topologicalKrullDim_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i)
        exact ⟨ZTensorPower.basis b (m : ℤ) (), (ZTensorPower.basis b (m : ℤ)).ne_zero _,
          fun h => absurd h hi⟩
    choose σ hσ0 hσres using hex
    exact ⟨W, hyW, τ, hτ, σ, (hRI m hm hmC W τ hτ).2 σ hσres hσ0,
      (exists_isLogResiduePresentation_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq hm hmC
        hτ σ hσres).2⟩
  refine ⟨m, hm, fun Γ => ?_, fun x => ?_⟩
  · by_cases hΓ0 : Δ Γ = 0
    · rw [hΓ0, mul_zero]; rfl
    obtain ⟨i, t, ht⟩ := exists_mem_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
      hΘ huniq Γ.1.genericPoint
    have hcohT : Order.coheight ((N.n i).base t) = 1 := by rw [ht]; exact Γ.1.coheight_genericPoint
    have hmono : StrictMono (N.n i).base := fun a b hab =>
      MMP.Intersection.lt_of_specializes_of_ne (hab.le.map (N.n i).base.hom.continuous)
        (fun h => hab.ne ((N.n i).isClosedEmbedding.injective h))
    have hle := Order.coheight_le_coheight_apply_of_strictMono _ hmono t
    rw [hcohT] at hle
    have hne : t ≠ genericPoint (N.X i) := by
      rintro rfl
      rw [coheight_genericPoint_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i]
        at hcohT
      exact zero_ne_one hcohT
    have hge : 1 ≤ Order.coheight t := by
      have hlt : t < genericPoint (N.X i) :=
        MMP.Intersection.lt_of_specializes_of_ne (genericPoint_specializes t) hne
      exact le_add_self.trans (Order.coheight_add_one_le hlt)
    have h1 : Order.coheight t = 1 := le_antisymm hle hge
    set Q : MMP.Mori.PrimeDivisor (N.X i) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne t h1
    have hQt : Q.genericPoint = t := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    -- `Θᵢ(Q) = [Q ⊆ D] + Δ(Γ)`
    have hcoef := hΔ i Q
    unfold adjointBoundaryCoeff at hcoef
    rw [Finset.sum_eq_single Γ] at hcoef
    · rw [if_pos (show (N.n i).base Q.genericPoint = Γ.1.genericPoint by rw [hQt, ht])]
        at hcoef
      -- `m Θᵢ(Q)` is an integer
      obtain ⟨W, hW, τ, hτ, s, hgenOn, -⟩ := hloc (ι.base Γ.1.genericPoint)
      have hQW : ((Q.support : Set (N.X i)) ∩ ((N.n i) ⁻¹ᵁ (ι ⁻¹ᵁ W) : Set (N.X i))).Nonempty :=
        ⟨Q.genericPoint, by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
          show ι.base ((N.n i).base Q.genericPoint) ∈ W by rw [hQt, ht]; exact hW⟩
      have hg := (hgenOn.1 i).2 Q hQW
      have : (m : ℚ) * Δ Γ = ((-Q.ordForm (s i) -
          m * (if (N.n i).base Q.genericPoint ∈ (doubleIntersectionLocus T : Set T) then 1 else 0)
            : ℤ) : ℚ) := by
        push_cast
        split_ifs at hcoef ⊢ <;> linear_combination hg - (m : ℚ) * hcoef
      rw [this]
      exact Rat.den_intCast _
    · intro Γ' _ hne
      rw [if_neg]
      exact fun h => hne (Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (h.symm.trans (by rw [hQt, ht]))))
    · exact fun h => absurd (Finsupp.notMem_support_iff.mp h) hΓ0
  · obtain ⟨W, hW, τ, hτ, s, hgenOn, hpres⟩ := hloc (ι.base x)
    exact ⟨ι ⁻¹ᵁ W, hW, s, hgenOn, hpres⟩

/-- The generic point of a floor component lies on no other floor component. -/
private theorem genericPoint_notMem_iUnion_range_floorComponent (i : N.ι) :
    (N.n i).base (genericPoint (N.X i)) ∉ ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base := by
  intro hmem
  obtain ⟨j, hji, z, hz⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨P, hPr, -, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  have hrange : ∀ l, Set.range (N.n l).base = closure {(N.n l).base (genericPoint (N.X l))} :=
    fun l => by
      rw [← Set.image_singleton, (N.n l).isClosedEmbedding.closure_image_eq,
        (genericPoint_spec (N.X l)).def, Set.image_univ]
  have hc := closure_mem_irreducibleComponents_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT
    N Θ hΘ huniq i
  have hsub : closure {(N.n i).base (genericPoint (N.X i))} ⊆ Set.range (N.n j).base :=
    (N.n j).isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨z, hz⟩)
  have heq : Set.range (N.n i).base = Set.range (N.n j).base := by
    rw [hrange i]
    refine hsub.antisymm (hc.2 ?_ hsub)
    rw [hrange j]
    exact isIrreducible_singleton.closure
  have hPP : ((P i).support : Set X) = (P j).support := by
    rw [← hPr i, ← hPr j, Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp,
      TopCat.coe_comp, Set.range_comp, Set.range_comp, heq]
  exact hji (hPinj (primeDivisor_eq_of_support_eq hPP)).symm

/-- **Local generators of the adjoint of the floor are unique up to units.** Two local
generators `g, ρ` of `𝒪_T(m(K_T + Δ))` on `U` satisfy `g = ν^*e · ρ` for a unit `e` of
`𝒪_T(U)`: the floor is reduced, seminormal and `S₂`, its normalization components are closed
immersions with distinct generic points, and `Θᵢ` has coefficient one along the double locus. -/
private theorem exists_unit_smul_eq_of_isAdjointGeneratorOn_floor {m : ℕ} {U : T.Opens}
    {g ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m}
    (hg : IsAdjointGeneratorOn N n m Θ U g) (hρ : IsAdjointGeneratorOn N n m Θ U ρ) :
    ∃ e : Γ(T, U)ˣ, ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      g i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U (e : Γ(T, U))) •
        ρ i := by
  classical
  haveI := hB.charZero
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian ι
  obtain ⟨P, -, hPmem, hPinj, -⟩ :=
    exists_primeDivisor_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  haveI : Finite N.ι := Finite.of_injective
    (fun i => (⟨P i, hPmem i⟩ : {Q // Q ∈ B.roundDown.support}))
    fun a b h => hPinj (congrArg Subtype.val h)
  have hci : ∀ j, IsClosedImmersion (N.n j) :=
    isClosedImmersion_floorComponent ι N hΘ
  have hS2 := satisfiesS2_of_isCMScheme (isCMScheme_floor ι hdim hK hproj hQ hB hdlt hB0 hT)
  have hsn := isSeminormal_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  have hgen := genericPoint_notMem_iUnion_range_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT
    N Θ hΘ huniq
  have hdimN := topologicalKrullDim_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  have hΘ1 : ∀ i (Q : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base Q.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
        (Θ i).coeff Q = 1 := by
    intro i Q hQD
    obtain ⟨j, hij, Q', hQQ'⟩ := exists_primeDivisor_of_mem_doubleIntersectionLocus ι hdim hK hproj
      hQ hB hdlt hB0 hT N Θ hΘ huniq i Q hQD
    exact coeff_eq_one_of_mem_range ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq i j hij Q
      ⟨Q'.genericPoint, hQQ'.symm⟩
  obtain ⟨e₁, he₁⟩ := exists_smul_eq_of_isAdjointGeneratorOn N hS2 hsn hci hgen hdimN hΘ1 hg hρ
  obtain ⟨e₂, he₂⟩ := exists_smul_eq_of_isAdjointGeneratorOn N hS2 hsn hci hgen hdimN hΘ1 hρ hg
  have h12 : e₁ * e₂ = 1 := by
    refine sub_eq_zero.mp (eq_zero_of_forall_germToFunctionField_eq_zero N _ fun i hi => ?_)
    have h3 := he₁ i hi
    rw [he₂ i hi, smul_smul] at h3
    have h0 : (((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U e₁) *
        ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U e₂) - 1) • g i = 0 := by
      rw [sub_smul, ← h3, one_smul, sub_self]
    rw [map_sub, map_mul, map_one, map_sub, map_mul, map_one]
    exact (smul_eq_zero.mp h0).resolve_right (hg.1 i).1
  exact ⟨⟨e₁, e₂, h12, by rw [mul_comm]; exact h12⟩, he₁⟩

/-- **The floor is an sdlt adjoint pair.** -/
private theorem exists_isSdltAdjointPair :
    ∃ Δ : QWeilDivisor T, IsSdltAdjointPair N n Δ Θ := by
  obtain ⟨Δ, hΔb, hΔD, hΔΘ⟩ :=
    exists_isAdjointBoundary ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  exact ⟨Δ,
    { isNFold := isNFold_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
      isProjectiveMorphism :=
        Stacks.SectionsVanishingOnSubscheme.isProjectiveMorphism_comp_of_isClosedImmersion ι
          hproj.isProjective
      satisfiesS2 := satisfiesS2_of_isCMScheme (isCMScheme_floor ι hdim hK hproj hQ hB hdlt hB0 hT)
      isSeminormal := isSeminormal_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
      isNcInCodimOne := isNcInCodimOne_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
      isBoundary := hΔb
      genericPoint_not_mem_doubleIntersectionLocus := hΔD
      isAdjointBoundary := hΔΘ
      exists_isDltPair := exists_isDltPair_floorComponent ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
        hΘ huniq
      exists_isAdjointGeneratorOn := exists_isAdjointGeneratorOn_floor ι hdim hK hproj hQ hB hdlt
        hB0 hT N Θ hΘ huniq Δ hΔΘ }⟩

end Floor

end MMP.Fourfold.SdltFloor

namespace MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold.SdltFloor

/-- **The whole projective dlt floor has an sdlt adjoint.** Let `(X, B)` be an effective
rational `ℚ`-factorial projective dlt pair (`MMP.Fourfold.IsPair`, `MMP.Fourfold.IsQFactorial`,
`MMP.Intersection.IsDltPair`) of dimension `n + 1`, and `ι : T ⟶ X` the reduced closed subscheme
with support `⌊B⌋ ≠ 0`. Then
* `T` is Cohen–Macaulay (`MMP.Mori.IsCMScheme`);
* there are a normalization `ν : ⨿ᵢ Tᵢ ⟶ T` (`MMP.Flips.NormalizationComponents`), a boundary
  `Δ` on `T` and boundaries `Θᵢ` on the `Tᵢ` making `(T, Δ; K_T + Δ)` an sdlt adjoint pair of
  dimension `n` with `Θᵢ = Cᵢ + Δᵢ` (`MMP.Fourfold.IsSdltAdjointPair`);
* each `Tᵢ ⟶ X` is a closed immersion onto a prime component of `⌊B⌋` and
  `Θᵢ = Diff_{Tᵢ}(B - Tᵢ)` (`MMP.Fourfold.IsAdjunctionStep`), every prime component of `⌊B⌋`
  being the image of exactly one `Tᵢ`;
* for every `m > 0` with `m(K_X + B)` Cartier and every local generator `τ` of
  `𝒪_X(m(K_X + B))` on an open `W`, the Poincaré residues `ρᵢ` of `τ` along the `Tᵢ` meeting `W`
  exist, and any family of nonzero forms `ρᵢ` which are these residues along the `Tᵢ` meeting `W`
  is a local generator of the `m`-th adjoint sheaf on `ι⁻¹(W)`
  (`MMP.Fourfold.IsAdjointGeneratorOn`), and every local generator `g` of that adjoint sheaf on an
  open `U ⊆ ι⁻¹(W)` is `ν^*e · ρ` for a unit `e` of `𝒪_T(U)`: the adjoint invertible sheaf is
  precisely `𝒪_X(m(K_X + B))|_T`. -/
@[mmp "lem_fourfold_projective_dlt_floor_sdlt"]
public theorem isCMScheme_and_exists_isSdltAdjointPair_of_isDltPair
    {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ}
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX (n + 1)) {B : QDivisor X}
    (hproj : Mori.IsProjectiveVariety k sX) (hQ : IsQFactorial sX) (hB : IsPair sX B)
    (hdlt : MMP.Intersection.IsDltPair sX B) (hB0 : B.roundDown ≠ 0)
    {T : Scheme.{0}} (ι : T ⟶ X) [IsClosedImmersion ι] [IsReduced T]
    (hT : Set.range ι.base = ⋃ P ∈ B.roundDown.support, (P.support : Set X)) :
    IsCMScheme T ∧
      ∃ (hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite)
        (N : NormalizationComponents (ι ≫ sX) hfin) (Δ : QWeilDivisor T)
        (Θ : ∀ i, QDivisor (N.X i)),
        IsSdltAdjointPair N n Δ Θ ∧
        (∀ i, IsAdjunctionStep sX B (N.n i ≫ ι) (Θ i)) ∧
        (∀ P ∈ B.roundDown.support,
          ∃! i, Set.range (N.n i ≫ ι).base = (P.support : Set X)) ∧
        ∀ m : ℕ, 0 < m → ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor →
          ∀ (W : X.Opens) (τ : RationalPluriForms sX (n + 1) m), GeneratesOn B m W τ →
            (∃ ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m,
              ∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
                IsPoincareResidue sX (N.n i ≫ ι) n m τ (ρ i)) ∧
            ∀ ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m,
              (∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
                IsPoincareResidue sX (N.n i ≫ ι) n m τ (ρ i)) →
              (∀ i, ρ i ≠ 0) →
              IsAdjointGeneratorOn N n m Θ (ι ⁻¹ᵁ W) ρ ∧
              ∀ U : T.Opens, U ≤ ι ⁻¹ᵁ W →
                ∀ g : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sX) n m,
                  IsAdjointGeneratorOn N n m Θ U g →
                  ∃ e : Γ(T, U)ˣ, ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
                    g i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom
                      ((N.n i).app U (e : Γ(T, U))) • ρ i := by
  refine ⟨isCMScheme_floor ι hdim hK hproj hQ hB hdlt hB0 hT, ?_⟩
  obtain ⟨hfin, N, Θ, hΘ, huniq⟩ :=
    exists_normalizationComponents_isAdjunctionStep ι hdim hK hproj hQ hB hdlt hB0 hT
  obtain ⟨Δ, hΔ⟩ := exists_isSdltAdjointPair ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq
  refine ⟨hfin, N, Δ, Θ, hΔ, hΘ, huniq, fun m hm hC W τ hτ => ?_⟩
  obtain ⟨h1, h2⟩ := residueIdentification_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ hΘ huniq m hm hC
    W τ hτ
  refine ⟨h1, fun ρ hρ hρ0 => ⟨h2 ρ hρ hρ0, fun U hUW g hg => ?_⟩⟩
  have hρU : IsAdjointGeneratorOn N n m Θ U ρ := by
    obtain ⟨h3, h4⟩ := h2 ρ hρ hρ0
    exact ⟨fun i => (h3 i).mono fun z hz => hUW hz,
      fun i j Q Q' e₁ e₂ e₃ e₄ => h4 i j Q Q' e₁ (hUW e₂) e₃ e₄⟩
  exact exists_unit_smul_eq_of_isAdjointGeneratorOn_floor ι hdim hK hproj hQ hB hdlt hB0 hT N Θ
    hΘ huniq hg hρU

end MMP.Fourfold
