module

public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingChartTower

/-!
# The divisorial sheaf is quasi-coherent

Let `X` be a Noetherian normal scheme and `D` a divisor on `X`. The divisorial sheaf `𝒪_X(D)`
is quasi-coherent: for every open `U` of `X` and every `a ∈ Γ(X, U)`, the restriction
`𝒪_X(D)(U) → 𝒪_X(D)(X_a)` is the localization away from `a`.

Indeed, a section `ψ` of `𝒪_X(D)` over `X_a` extends to `U` after multiplication by a power of
`a`: on the irreducible components meeting `X_a` the extension is `aⁿψ`, and it is zero on the
others. The only prime divisors `E` meeting `U` at which `aⁿψ` might fail the condition
`v_E(aⁿψ) + d_E ≥ 0` are those not meeting `X_a`, on a component meeting `X_a`; these are the
codimension-one points of the closures of the generic points of the components outside `X_a`,
finitely many, and `v_E(a) ≥ 1` along each of them, so a large `n` works. Conversely a section
over `U` vanishing on `X_a` is killed by `a`, since `a` vanishes at the generic point of every
component not meeting `X_a`, the local rings there being fields.

## Main results

* `MMP.Mori.Divisor.isLocalizedModule_divisorialSheaf_restrictₗ`: the sections of `𝒪_X(D)` over
  `X_a` are the localization away from `a` of its sections over `U`.
* `MMP.Mori.Divisor.isQuasicoherent_divisorialSheaf`: `𝒪_X(D)` is quasi-coherent.

## Implementation notes

Quasi-coherence is obtained from the criterion
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`,
which needs the localization property only over affine opens; it holds here over every open.

## References

* [R. Hartshorne, *Algebraic geometry*][Har77], II.6
* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Order
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace MMP.Mori

variable {X : Scheme.{u}}

/-- On a reduced scheme, a nonzero element of a factor `𝒪_{X,η_Z}` of `K(X)` is a unit. -/
theorem isUnit_of_ne_zero_stalk [IsReduced X] (Z : irreducibleComponents X)
    {f : X.presheaf.stalk (componentGenericPoint X Z)} (hf : f ≠ 0) : IsUnit f := by
  obtain ⟨g, hg⟩ := (RationalFunctions.isField_stalk X Z).mul_inv_cancel hf
  exact ⟨⟨f, g, hg, by rw [mul_comm]; exact hg⟩, rfl⟩

namespace PrimeDivisor

variable [IsLocallyNoetherian X] [IsNormal X] (E : PrimeDivisor X)

/-- An element of the maximal ideal of `𝒪_{X,E}` has order at least `1` along `E`. -/
theorem ordGE_one_toComponent {b : E.localRing}
    (hb : b ∈ IsLocalRing.maximalIdeal E.localRing) : E.OrdGE 1 (E.toComponent.hom b) := by
  by_cases h0 : E.toComponent.hom b = 0
  · exact Or.inl h0
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  have hc : c ≠ 0 := by
    rintro rfl
    exact h0 (by rw [mul_zero, map_zero])
  refine Or.inr ?_
  rw [map_mul, map_mul, E.valuation_toComponent_of_irreducible hϖ]
  exact le_mul_of_one_le_right' (E.one_le_valuation_toComponent hc)

/-- Every element of the factor `𝒪_{X,η_{i(E)}}` of `K(X)` has some lower bound on its order
along `E`. -/
theorem exists_ordGE (f : X.presheaf.stalk (componentGenericPoint X E.component)) :
    ∃ k : ℤ, E.OrdGE k f := by
  by_cases hf : f = 0
  · exact ⟨0, Or.inl hf⟩
  have hu : IsUnit f := isUnit_of_ne_zero_stalk E.component hf
  have hv : E.valuation f ≠ 0 := (hu.map E.valuation).ne_zero
  exact ⟨WithZero.log (E.valuation f), Or.inr (WithZero.exp_log hv).le⟩

variable {E}

/-- If `f` has order at least `n` along `E`, then `f ^ k` has order at least `k * n`. -/
theorem OrdGE.pow {n : ℤ} {f : X.presheaf.stalk (componentGenericPoint X E.component)}
    (hf : E.OrdGE n f) (k : ℕ) : E.OrdGE (k * n) (f ^ k) := by
  induction k with
  | zero =>
    refine Or.inr ?_
    simp only [pow_zero, map_one, Nat.cast_zero, zero_mul, WithZero.exp_zero, le_refl]
  | succ k ih =>
    rw [pow_succ]
    refine (ih.mul hf).mono (le_of_eq ?_)
    push_cast
    ring

end PrimeDivisor

namespace Divisor

/-- On a reduced scheme a section `a` over `U` vanishes at the generic point of every
irreducible component meeting `U` but not `X_a`. -/
theorem germ_eq_zero_of_notMem_basicOpen [IsReduced X] {U : X.Opens} (a : Γ(X, U))
    {Z : irreducibleComponents X} (hZ : componentGenericPoint X Z ∈ U)
    (ha : componentGenericPoint X Z ∉ X.basicOpen a) :
    X.presheaf.germ U _ hZ a = 0 := by
  by_contra h
  exact ha ((Scheme.mem_basicOpen X a _ hZ).mpr
    (isUnit_of_ne_zero_stalk Z h))

variable [IsLocallyNoetherian X] [IsNormal X]

omit [IsNormal X] in
/-- On a Noetherian scheme, only finitely many prime divisors lie on an irreducible component
meeting `X_a` without meeting `X_a` themselves. -/
theorem finite_primeDivisor_notMem_basicOpen [CompactSpace X] {U : X.Opens} (a : Γ(X, U)) :
    {E : PrimeDivisor X | E.genericPoint ∉ X.basicOpen a ∧
      componentGenericPoint X E.component ∈ X.basicOpen a}.Finite := by
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have : Finite (irreducibleComponents X) :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  have hfin : (⋃ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ X.basicOpen a},
      {z : X | z ∈ closure {componentGenericPoint X Z.1} ∧ z ∉ X.basicOpen a ∧
        coheight z = 1}).Finite :=
    Set.finite_iUnion fun Z => finite_coheight_eq_one_mem_closure_notMem _ _ Z.2
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨E, ⟨hE, hEZ⟩, rfl⟩
  refine Set.mem_iUnion.mpr ⟨⟨E.component, hEZ⟩, ?_, hE, E.coheight_genericPoint⟩
  rw [(isGenericPoint_componentGenericPoint X E.component).def]
  exact E.genericPoint_mem_component

/-- A section of `𝒪_X(D)` over `V`, as a section of `𝒦_X` over `V`. -/
abbrev secVal (D : Divisor X) (V : X.Opens) (ψ : Γ(D.divisorialSheaf, V)) :
    ToType ((rationalFunctionsPresheaf X).obj (op V)) :=
  (ψ : D.divisorialSubmodule V).1

variable [CompactSpace X]

/-- **The sections of `𝒪_X(D)` over `X_a` are a localization.** For an open `U` of a Noetherian
normal scheme and `a ∈ Γ(X, U)`, the restriction `𝒪_X(D)(U) → 𝒪_X(D)(X_a)` is the localization
away from `a`. -/
theorem isLocalizedModule_divisorialSheaf_restrictₗ (D : Divisor X) {U : X.Opens} (a : Γ(X, U)) :
    letI := moduleOfLE D.divisorialSheaf (X.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ D.divisorialSheaf (X.basicOpen_le a)) := by
  classical
  letI := moduleOfLE D.divisorialSheaf (X.basicOpen_le a)
  let V := X.basicOpen a
  have hVU : V ≤ U := X.basicOpen_le a
  have hsmul : ∀ (r : Γ(X, U)) (ψ : Γ(D.divisorialSheaf, V))
      (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V}),
      secVal D V (r • ψ) Z = X.presheaf.germ U _ (hVU Z.2) r * secVal D V ψ Z := by
    intro r ψ Z
    change X.presheaf.germ V _ Z.2 (X.presheaf.map (homOfLE hVU).op r) * _ = _
    rw [TopCat.Presheaf.germ_res_apply]
  have hsmulU : ∀ (r : Γ(X, U)) (φ : Γ(D.divisorialSheaf, U))
      (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}),
      secVal D U (r • φ) Z = X.presheaf.germ U _ Z.2 r * secVal D U φ Z :=
    fun _ _ _ => rfl
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · have hu : IsUnit (X.presheaf.map (homOfLE hVU).op a) :=
      X.toRingedSpace.isUnit_res_basicOpen a
    have ha : ∀ ψ : Γ(D.divisorialSheaf, V),
        a • ψ = (X.presheaf.map (homOfLE hVU).op a) • ψ := fun _ => rfl
    refine (Module.End.isUnit_iff _).mpr ⟨fun ψ₁ ψ₂ h => ?_, fun ψ => ?_⟩
    · simp only [Module.algebraMap_end_apply, ha] at h
      exact (hu.smul_left_cancel).mp h
    · refine ⟨((hu.unit⁻¹ : (Γ(X, V))ˣ) : Γ(X, V)) • ψ, ?_⟩
      simp only [Module.algebraMap_end_apply, ha]
      change (hu.unit : Γ(X, V)) • ((hu.unit⁻¹ : (Γ(X, V))ˣ) : Γ(X, V)) • ψ = ψ
      rw [smul_smul, hu.unit.mul_inv, one_smul]
  · intro ψ
    let ψ' : D.divisorialSubmodule V := ψ
    set T := {E : PrimeDivisor X | E.genericPoint ∉ X.basicOpen a ∧
      componentGenericPoint X E.component ∈ X.basicOpen a}
    have hT : T.Finite := finite_primeDivisor_notMem_basicOpen a
    let k : PrimeDivisor X → ℤ := fun E =>
      if h : componentGenericPoint X E.component ∈ V then
        (E.exists_ordGE (ψ'.1 ⟨E.component, h⟩)).choose else 0
    let n : ℕ := hT.toFinset.sup fun E => (-D.coeff E - k E).toNat
    let φ : ToType ((rationalFunctionsPresheaf X).obj (op U)) := fun Z =>
      if h : componentGenericPoint X Z.1 ∈ V then
        X.presheaf.germ U _ Z.2 a ^ n * ψ'.1 ⟨Z.1, h⟩ else 0
    have hφ : D.IsDivisorialSection U φ := by
      intro E hEU
      have hηU := E.componentGenericPoint_mem_of_nonempty hEU
      have hEgU := E.genericPoint_mem_of_nonempty hEU
      have hgerm : X.presheaf.germ U _ hηU a =
          E.toComponent.hom (X.presheaf.germ U _ hEgU a) :=
        (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hEgU
          E.specializes_genericPoint a).symm
      change E.OrdGE _ (if h : componentGenericPoint X E.component ∈ V then
        X.presheaf.germ U _ hηU a ^ n * ψ'.1 ⟨E.component, h⟩ else 0)
      split_ifs with h
      · by_cases hEV : (E.support ∩ V).Nonempty
        · rw [hgerm, ← map_pow]
          exact (ψ'.2 E hEV).toComponent_mul _
        · have hgen : E.genericPoint ∉ V := fun hg =>
            hEV ⟨E.genericPoint, by
              rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
              exact subset_closure rfl, hg⟩
          have hET : E ∈ T := ⟨hgen, h⟩
          have hmax : X.presheaf.germ U _ hEgU a ∈
              IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) := fun hunit =>
            hgen ((Scheme.mem_basicOpen X a _ hEgU).mpr hunit)
          have h1 : E.OrdGE 1 (X.presheaf.germ U _ hηU a) := by
            rw [hgerm]
            exact E.ordGE_one_toComponent hmax
          have hk : E.OrdGE (k E) (ψ'.1 ⟨E.component, h⟩) := by
            simp only [k, dif_pos h]
            exact (E.exists_ordGE _).choose_spec
          refine ((h1.pow n).mul hk).mono ?_
          have hn : (-D.coeff E - k E).toNat ≤ n :=
            Finset.le_sup (f := fun E => (-D.coeff E - k E).toNat) (hT.mem_toFinset.mpr hET)
          have := Int.self_le_toNat (-D.coeff E - k E)
          omega
      · exact PrimeDivisor.OrdGE.zero _
    refine ⟨n, (⟨φ, hφ⟩ : D.divisorialSubmodule U), Subtype.ext (funext fun Z => ?_)⟩
    change secVal D V (a ^ n • ψ) Z = φ ⟨Z.1, hVU Z.2⟩
    rw [hsmul]
    simp only [φ]
    rw [dif_pos (show componentGenericPoint X Z.1 ∈ V from Z.2), map_pow]
  · intro φ hφ
    refine ⟨1, Subtype.ext (funext fun Z => ?_)⟩
    change secVal D U (a ^ 1 • φ) Z = 0
    rw [hsmulU, pow_one]
    by_cases hZ : componentGenericPoint X Z.1 ∈ V
    · have := congrFun (congrArg Subtype.val hφ) ⟨Z.1, hZ⟩
      exact mul_eq_zero_of_right _ this
    · rw [germ_eq_zero_of_notMem_basicOpen a Z.2 hZ, zero_mul]

/-- **The divisorial sheaf is quasi-coherent.** On a Noetherian normal scheme `X`, the
divisorial sheaf `𝒪_X(D)` of every divisor `D` is a quasi-coherent `𝒪_X`-module. -/
instance isQuasicoherent_divisorialSheaf (D : Divisor X) : D.divisorialSheaf.IsQuasicoherent :=
  Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ _
    fun _ _ a => isLocalizedModule_divisorialSheaf_restrictₗ D a

end Divisor

end MMP.Mori

end
