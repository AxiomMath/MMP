module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import MMP.RingTheory.RegularLocalRing.SymbolicPower
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.Components
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoStepTower
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.StalkwiseRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreChart
public import StacksFrontier.Topology.Dimension.Codimension

/-!
# Orders of ideals, marked ideals and their transforms (Kollár, *Resolution*, 3.47–3.60)

Let `X` be a smooth scheme and `I ⊆ 𝒪_X` a coherent ideal sheaf. The *order* `ord_x I` of `I`
at a point `x` is the largest `r` with `I·𝒪_{x,X} ⊆ 𝔪_x^r`; along an irreducible closed subset
`Z` it is the order at the generic point, and for a reducible `Z` one says `ord_Z I ≥ m`
(`= m`) if this holds along every irreducible component (Kollár Def. 3.47). A *marked ideal*
is a pair `(I, m)` with `m ∈ ℕ`; its *birational transform* under the blow-up `π : B_ZX → X`
of a smooth center with `ord_Z I ≥ m` is `(𝒪_{B_ZX}(mF)·π^*I, m)`, `F = π⁻¹(Z)` (Def. 3.48,
3.60), and the *controlled transform* of an ideal is `𝒪_{B_ZX}(∑ m_j F_j)·π^*I`, `m_j` the
order of `I` along the components `Z_j` of `Z` (3.58). This file states these notions, together
with sums and products of marked ideals and marked functions (Def. 3.59), the coordinate charts
of a blow-up and the chart transform of a marked function (3.60.2–3), local coordinates on an
open set, the divisorial part `Div(I)` of an ideal (Def. 3.48), and the completion of a scheme
at a point and fields of representatives (Def. 3.55).

## Main definitions

* `MMP.Resolution.orderAlong`, `MMP.Resolution.OrderAlongGE`, `MMP.Resolution.OrderAlongEq`,
  `MMP.Resolution.maxOrderAlong`, `MMP.Resolution.maxOrder`: `ord_Z I`, `ord_Z I ≥ m`,
  `ord_Z I = m`, `maxord_Z I` and `maxord I`.
* `MMP.Resolution.MarkedIdeal` with `cosupport`, `+` and `*`.
* `MMP.Resolution.MarkedFunction`.
* `MMP.Resolution.IsLocalCoordinates`.
* `MMP.Resolution.BlowupChartData`, `…chart`, `…chartTransform`.
* `MMP.Resolution.idealColon`, `MMP.Resolution.MarkedIdeal.birationalTransform`,
  `MMP.Resolution.controlledTransform`.
* `MMP.Resolution.divisorialPart`, `MMP.Resolution.divisorialPartIdeal`.
* `MMP.Resolution.completionAtPoint`, `MMP.Resolution.IsFieldOfRepresentatives`.

## Implementation notes

The order at a point is `MMP.Resolution.multAt` (`ord(I_x)` in the local ring `𝒪_{x,X}`,
`MMP.Resolution.idealOrder`), and the order of a function is `MMP.Resolution.mult`; both are
registered below, not restated. The completion `R̂ = lim R/𝔪^s` of a local ring is Mathlib's
`AdicCompletion (maximalIdeal R) R`, with `AdicCompletion.of` and `AdicCompletion.eval`
(recorded, not restated). Irreducible components of a subset are
`MMP.Resolution.componentsOf` (maximal irreducible subsets), each with its reduced structure
`MMP.Resolution.componentsFamily`.

The divisors `𝒪(mF)·π^*I` and `𝒪(∑ m_jF_j)·π^*I` are ideal sheaves because `π^*I` is divisible
by `𝒪(-mF)` (resp. `𝒪(-∑ m_jF_j)`), an invertible ideal. They are defined as the ideal
quotients `(π^*I : 𝒪(-mF))`, the largest quasi-coherent ideal sheaf contained in the ideal
quotients on affine opens (`Scheme.IdealSheafData.ofIdeals`), with `𝒪(-F_j)` the ideal of the
scheme-theoretic inverse image of `Z_j` with its reduced structure. That they multiply back to
`π^*I` is stated as a theorem (`…_mul_eq`).

The `ℓ`-th chart `U_ℓ = D_+(x_ℓ) ⊆ π⁻¹(U)` of the blow-up over an open `U` is the union, over
the affine opens `V ⊆ U`, of the standard charts `D_+(x_ℓ|_V)` of `π⁻¹(V)`
(`AlgebraicGeometry.blowUpChartOpen`); this is `D_+(x_ℓ) ∩ π⁻¹(V)` for each `V`.

Hypotheses of the source that only restrict the domain are dropped where the definition makes
sense without them: smoothness of `X` (and of the center) for marked ideals, marked functions,
transforms and charts, local noetherianity for orders, closedness of `Z` in `ord_Z`, and
finiteness of `ord_{Z_j} I` in the controlled transform (an infinite order is read as `0`).

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.47–3.60]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

/-! ### Notions recorded from the library -/

attribute [mmp "def_kr3c_order_at_point"] MMP.Resolution.multAt MMP.Resolution.mult
  MMP.Resolution.idealOrder

namespace MMP.Resolution

/-! ### Orders -/

section Order

variable {X : Scheme.{u}}

/-- The *order* `ord_Z I = ord_η I` of an ideal sheaf `I` along an irreducible subset `Z ⊆ X`
with generic point `η` (Kollár Def. 3.47). -/
@[mmp "def_kr3c_order_along_irreducible"]
def orderAlong (I : X.IdealSheafData) {Z : Set X} (hZ : IsIrreducible Z) : ℕ∞ :=
  multAt I hZ.genericPoint

/-- `ord_Z I ≥ m` for a closed subset `Z ⊆ X` (Kollár Def. 3.47): `ord_{Z_j} I ≥ m` along every
irreducible component `Z_j` of `Z` (vacuous for `Z = ∅`). -/
@[mmp "def_kr3c_order_along_closed_ge"]
def OrderAlongGE (I : X.IdealSheafData) (Z : Set X) (m : ℕ∞) : Prop :=
  ∀ W (hW : W ∈ componentsOf Z), m ≤ orderAlong I hW.1.1

/-- `ord_Z I = m` for a closed subset `Z ⊆ X` (Kollár Def. 3.47): `ord_{Z_j} I = m` along every
irreducible component `Z_j` of `Z`. -/
@[mmp "def_kr3c_order_along_closed_eq"]
def OrderAlongEq (I : X.IdealSheafData) (Z : Set X) (m : ℕ∞) : Prop :=
  ∀ W (hW : W ∈ componentsOf Z), orderAlong I hW.1.1 = m

/-- The *maximal order* `maxord_Z I = sup {ord_z I : z ∈ Z}` of `I` along a subset `Z ⊆ X`, with
`sup ∅ = 0` (Kollár Def. 3.47). -/
@[mmp "def_kr3c_maximal_order_along"]
def maxOrderAlong (I : X.IdealSheafData) (Z : Set X) : ℕ∞ :=
  ⨆ z ∈ Z, multAt I z

/-- The maximal order `maxord I = maxord_X I` of `I` on all of `X`. -/
@[mmp "def_kr3c_maximal_order_along"]
def maxOrder (I : X.IdealSheafData) : ℕ∞ :=
  maxOrderAlong I Set.univ

/-- The closure of an irreducible subset, as an irreducible closed subset. -/
def irreducibleClosure {T : Type*} [TopologicalSpace T] {W : Set T} (hW : IsIrreducible W) :
    IrreducibleCloseds T :=
  ⟨closure W, hW.closure, isClosed_closure⟩

/-- Every irreducible component of `Z ⊆ X` has codimension `≥ 1` in `X`. -/
def HasComponentsOfPositiveCodim (Z : Set X) : Prop :=
  ∀ W (hW : W ∈ componentsOf Z), 1 ≤ codimension (irreducibleClosure hW.1.1)

end Order

/-! ### Marked ideals and marked functions -/

/-- A *marked ideal sheaf* `(I, m)` on `X` (Kollár Def. 3.48 = Def. 3.59): an ideal sheaf
`I ⊆ 𝒪_X` and a marking `m ∈ ℕ`. (On a smooth, hence locally noetherian, scheme every
quasi-coherent ideal sheaf is coherent.) -/
@[mmp "def_kr3c_marked_ideal"]
structure MarkedIdeal (X : Scheme.{u}) where
  /-- The ideal sheaf `I`. -/
  I : X.IdealSheafData
  /-- The marking `m`. -/
  m : ℕ

namespace MarkedIdeal

variable {X : Scheme.{u}}

/-- The *cosupport* `cosupp(I, m) = {x ∈ X : ord_x I ≥ m}` of a marked ideal (Kollár
Def. 3.59). -/
@[mmp "def_kr3c_marked_cosupport"]
def cosupport (a : MarkedIdeal X) : Set X :=
  {x | (a.m : ℕ∞) ≤ multAt a.I x}

/-- A point lies in `cosupp(I, m)` iff `ord_x I ≥ m`. -/
theorem mem_cosupport {a : MarkedIdeal X} {x : X} :
    x ∈ a.cosupport ↔ (a.m : ℕ∞) ≤ multAt a.I x := Iff.rfl

/-- The *sum* `(I₁, m) + (I₂, m) = (I₁ + I₂, m)` of marked ideals with the same marking (Kollár
Def. 3.59); the marking of the sum is that of the first summand. -/
@[mmp "def_kr3c_marked_ideal_sum"]
instance : Add (MarkedIdeal X) where
  add a b := ⟨a.I + b.I, a.m⟩

/-- The sum of marked ideals `a + b` is `(a.I + b.I, a.m)`. -/
@[mmp "def_kr3c_marked_ideal_sum"]
theorem add_def (a b : MarkedIdeal X) : a + b = ⟨a.I + b.I, a.m⟩ := rfl

@[simp] theorem add_I (a b : MarkedIdeal X) : (a + b).I = a.I + b.I := rfl

@[simp] theorem add_m (a b : MarkedIdeal X) : (a + b).m = a.m := rfl

/-- The *product* `(I₁, m₁)·(I₂, m₂) = (I₁I₂, m₁ + m₂)` of marked ideals (Kollár Def. 3.59). -/
@[mmp "def_kr3c_marked_ideal_product"]
instance : Mul (MarkedIdeal X) where
  mul a b := ⟨a.I * b.I, a.m + b.m⟩

/-- The product of marked ideals `a * b` is `(a.I * b.I, a.m + b.m)`. -/
@[mmp "def_kr3c_marked_ideal_product"]
theorem mul_def (a b : MarkedIdeal X) : a * b = ⟨a.I * b.I, a.m + b.m⟩ := rfl

@[simp] theorem mul_I (a b : MarkedIdeal X) : (a * b).I = a.I * b.I := rfl

@[simp] theorem mul_m (a b : MarkedIdeal X) : (a * b).m = a.m + b.m := rfl

end MarkedIdeal

/-- A *marked function* `(f, m)` on `X` (Kollár Def. 3.59): a section `f ∈ 𝒪_X(U)` over some
open `U ⊆ X` and a marking `m ∈ ℕ`. -/
@[mmp "def_kr3c_marked_function"]
structure MarkedFunction (X : Scheme.{u}) where
  /-- The open set `U` on which `f` is defined. -/
  U : X.Opens
  /-- The section `f ∈ 𝒪_X(U)`. -/
  f : Γ(X, U)
  /-- The marking `m`. -/
  m : ℕ

/-! ### Local coordinates -/

/-- A *system of local coordinates on* an open `U` of a scheme `X` over `k` (Kollár (3.60.2)):
sections `x_1, …, x_n ∈ 𝒪_X(U)` such that `(x_1, …, x_n) : U → 𝔸^n_k` is étale (the coordinates
of `𝔸^n_k` being indexed by `ULift (Fin n)`, for universe reasons). -/
@[mmp "def_kr3c_local_coordinates"]
def IsLocalCoordinates {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (U : X.Opens) {n : ℕ} (x : Fin n → Γ(X, U)) : Prop :=
  Etale (AffineSpace.homOfVector (n := ULift.{u} (Fin n)) (U.ι ≫ sX)
    fun i => U.topIso.inv.hom (x i.down))

/-! ### Coordinate charts of a blow-up -/

/-- An open `U ⊆ X` with sections `x_1, …, x_r ∈ 𝒪_X(U)` generating `I_Z|_U` (Kollár
(3.60.2)): on every affine open `V ⊆ U`, `I_Z(V)` is generated by the restrictions of the
`x_i`. -/
@[mmp "def_kr3c_blowup_chart"]
structure BlowupChartData {X : Scheme.{u}} (Z : X.IdealSheafData) where
  /-- The open set `U`. -/
  U : X.Opens
  /-- The number `r` of generators. -/
  r : ℕ
  /-- The generators `x_1, …, x_r ∈ 𝒪_X(U)`. -/
  x : Fin r → Γ(X, U)
  /-- On every affine open `V ⊆ U`, `I_Z(V)` is generated by the restrictions of the `x_i`. -/
  generates : ∀ (V : X.affineOpens) (h : V.1 ≤ U),
    Z.ideal V = Ideal.span (Set.range fun i => (X.presheaf.map (homOfLE h).op).hom (x i))

namespace BlowupChartData

variable {X : Scheme.{u}} {Z : X.IdealSheafData} (c : BlowupChartData Z)

/-- On every affine open `V ⊆ U`, the restriction of each generator `x_ℓ` lies in `I_Z(V)`. -/
theorem restrict_mem_ideal (V : X.affineOpens) (h : V.1 ≤ c.U) (ℓ : Fin c.r) :
    (X.presheaf.map (homOfLE h).op).hom (c.x ℓ) ∈ Z.ideal V := by
  rw [c.generates V h]
  exact Ideal.subset_span ⟨ℓ, rfl⟩

/-- The `ℓ`-th *chart* `U_ℓ = D_+(x_ℓ) ⊆ π⁻¹(U)` of the blow-up `π : B_ZX → X` (Kollár
(3.60.2)): the union over the affine opens `V ⊆ U` of the standard charts `D_+(x_ℓ|_V)` of
`π⁻¹(V) = Proj ⨁_d I_Z(V)^d`. -/
@[mmp "def_kr3c_blowup_chart"]
def chart (ℓ : Fin c.r) : (blowUp Z).Opens :=
  ⨆ (V : X.affineOpens) (h : V.1 ≤ c.U),
    (blowUpChartOpen Z V ⟨_, c.restrict_mem_ideal V h ℓ⟩).1

/-- The chart `U_ℓ` lies in `π⁻¹(U)`. -/
@[mmp "def_kr3c_blowup_chart"]
theorem chart_le (ℓ : Fin c.r) : c.chart ℓ ≤ blowUpToBase Z ⁻¹ᵁ c.U :=
  iSup₂_le fun V h => (blowUpChartOpen_le Z V _).trans fun _ hx => h hx

/-- The pull-back `π^*f ∈ 𝒪_{B_ZX}(U_ℓ)` of a section `f ∈ 𝒪_X(U)` to the chart `U_ℓ`. -/
@[mmp "def_kr3c_blowup_chart"]
def chartPullback (ℓ : Fin c.r) (f : Γ(X, c.U)) : Γ(blowUp Z, c.chart ℓ) :=
  ((blowUpToBase Z).appLE c.U (c.chart ℓ) (c.chart_le ℓ)).hom f

end BlowupChartData

open Opposite in
/-- A nonzerodivisor on an affine open stays one on every smaller open. -/
private theorem restrict_mem_nonZeroDivisors {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W)
    {g : Γ(Y, W)} (hg : g ∈ nonZeroDivisors Γ(Y, W)) {O : Y.Opens} (h : O ≤ W) :
    Y.presheaf.map (homOfLE h).op g ∈ nonZeroDivisors Γ(Y, O) := by
  have key : ∀ x : Γ(Y, O), x * Y.presheaf.map (homOfLE h).op g = 0 → x = 0 := by
    intro x hx
    have hs : ∀ p : O, ∃ s : Γ(Y, W), Y.basicOpen s ≤ O ∧ (p : Y) ∈ Y.basicOpen s :=
      fun p => hW.exists_basicOpen_le p (h p.2)
    choose s hsO hps using hs
    refine Y.sheaf.eq_of_locally_eq' (fun p : O => Y.basicOpen (s p)) O
      (fun p => homOfLE (hsO p)) ?_ x 0 ?_
    · intro p hp
      exact Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hps ⟨p, hp⟩⟩
    · intro p
      have hD : Y.basicOpen (s p) ≤ W := Y.basicOpen_le _
      have := hW.isLocalization_basicOpen (s p)
      have hreg : IsSMulRegular Γ(Y, W) g := (isRegular_iff_mem_nonZeroDivisors.mpr hg).left
      have hreg' := IsSMulRegular.of_isLocalization (S := Γ(Y, Y.basicOpen (s p)))
        (Submonoid.powers (s p)) hreg
      have hmap : algebraMap Γ(Y, W) Γ(Y, Y.basicOpen (s p)) g =
          Y.presheaf.map (homOfLE hD).op g := rfl
      have h2 : Y.presheaf.map (homOfLE (hsO p)).op x *
          algebraMap Γ(Y, W) Γ(Y, Y.basicOpen (s p)) g = 0 := by
        rw [hmap]
        have e : Y.presheaf.map (homOfLE hD).op g =
            Y.presheaf.map (homOfLE (hsO p)).op (Y.presheaf.map (homOfLE h).op g) := by
          rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]; rfl
        rw [e, ← map_mul, hx, map_zero]
      rw [map_zero]
      apply hreg'
      refine Eq.trans ?_ (mul_zero (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen (s p)) g)).symm
      exact (mul_comm _ _).trans h2
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm]), key⟩

open Opposite in
private theorem existsUnique_fraction_of_cover {Y : Scheme.{u}} {V : Y.Opens} {ι : Type*}
    (W : ι → Y.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hle : ∀ i, W i ≤ V)
    (hcover : V ≤ ⨆ i, W i) (g f : Γ(Y, V))
    (hg : ∀ i, Y.presheaf.map (homOfLE (hle i)).op g ∈ nonZeroDivisors Γ(Y, W i))
    (hex : ∀ i, ∃ w : Γ(Y, W i),
      Y.presheaf.map (homOfLE (hle i)).op f = w * Y.presheaf.map (homOfLE (hle i)).op g) :
    ∃! y : Γ(Y, V), f = y * g := by
  choose w hw using hex
  have uniq : ∀ y y' : Γ(Y, V), f = y * g → f = y' * g → y = y' := by
    intro y y' h1 h2
    refine Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hle i)) hcover y y' fun i => ?_
    have e1 : Y.presheaf.map (homOfLE (hle i)).op y * Y.presheaf.map (homOfLE (hle i)).op g =
        Y.presheaf.map (homOfLE (hle i)).op y' * Y.presheaf.map (homOfLE (hle i)).op g := by
      rw [← map_mul, ← map_mul, ← h1, ← h2]
    exact (mul_cancel_right_mem_nonZeroDivisors (hg i)).mp e1
  have compat : TopCat.Presheaf.IsCompatible Y.presheaf W w := by
    intro i j
    have hreg := restrict_mem_nonZeroDivisors (hW i) (hg i) (inf_le_left : W i ⊓ W j ≤ W i)
    have hres : ∀ s : Γ(Y, V),
        Y.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op
            (Y.presheaf.map (homOfLE (hle i)).op s) =
          Y.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op
            (Y.presheaf.map (homOfLE (hle j)).op s) := by
      intro s
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Y.presheaf.map_comp,
        ← Y.presheaf.map_comp]
      rfl
    refine (mul_cancel_right_mem_nonZeroDivisors hreg).mp ?_
    calc _ = Y.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op
            (Y.presheaf.map (homOfLE (hle i)).op f) := by rw [hw i, map_mul]; try rfl
      _ = Y.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op
            (Y.presheaf.map (homOfLE (hle j)).op f) := hres f
      _ = _ := by rw [hw j, map_mul, hres g]; try rfl
  obtain ⟨y₀, hy, -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hle i)) hcover w compat
  let y : Γ(Y, V) := y₀
  have hfy : f = y * g := by
    refine Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hle i)) hcover _ _ fun i => ?_
    change Y.presheaf.map (homOfLE (hle i)).op f = Y.presheaf.map (homOfLE (hle i)).op (y * g)
    have hy' : Y.presheaf.map (homOfLE (hle i)).op y = w i := hy i
    rw [map_mul, hw i, hy']
  exact ⟨y, hfy, fun y' hy' => uniq _ _ hy' hfy⟩

namespace BlowupChartData

variable {X : Scheme.{u}} {Z : X.IdealSheafData} (c : BlowupChartData Z)

/-- On the chart `U_ℓ` the degree-zero fractions `x_i/x_ℓ` are sections of `𝒪_{B_ZX}`: there is a
unique `y ∈ 𝒪_{B_ZX}(U_ℓ)` with `π^*x_i = y · π^*x_ℓ` (Kollár (3.60.2)). -/
@[mmp "def_kr3c_blowup_chart"]
theorem existsUnique_chartFraction (ℓ i : Fin c.r) :
    ∃! y : Γ(blowUp Z, c.chart ℓ), c.chartPullback ℓ (c.x i) = y * c.chartPullback ℓ (c.x ℓ) := by
  let ι := {V : X.affineOpens // V.1 ≤ c.U}
  let a : ∀ (v : ι) (j : Fin c.r), Z.ideal v.1 := fun v j => ⟨_, c.restrict_mem_ideal v.1 v.2 j⟩
  let W : ι → (blowUp Z).Opens := fun v => (blowUpChartOpen Z v.1 (a v ℓ)).1
  have hchart : c.chart ℓ = ⨆ v, W v := iSup_subtype' (p := fun V : X.affineOpens => V.1 ≤ c.U)
    (f := fun V h => (blowUpChartOpen Z V ⟨_, c.restrict_mem_ideal V h ℓ⟩).1)
  have hWle : ∀ v, W v ≤ c.chart ℓ := fun v => hchart ▸ le_iSup W v
  have F1 : ∀ (v : ι) (f : Γ(X, c.U)),
      (blowUp Z).presheaf.map (homOfLE (hWle v)).op (c.chartPullback ℓ f) =
        blowUpChartMap Z v.1 (a v ℓ) ((X.presheaf.map (homOfLE v.2).op) f) := by
    intro v f
    have e1 := Scheme.Hom.appLE_map (blowUpToBase Z) (c.chart_le ℓ) (homOfLE (hWle v)).op
    have e2 := Scheme.Hom.map_appLE (blowUpToBase Z) (blowUpChartOpen_le Z v.1 (a v ℓ))
      (homOfLE v.2).op
    exact congrArg (fun φ => φ.hom f) (e1.trans e2.symm)
  refine existsUnique_fraction_of_cover W (fun v => (blowUpChartOpen Z v.1 (a v ℓ)).2) hWle
    hchart.le _ _ ?_ ?_
  · intro v
    rw [F1]
    exact blowUpChartMap_self_mem_nonZeroDivisors Z v.1 (a v ℓ)
  · intro v
    obtain ⟨w, hw⟩ := exists_mul_eq_blowUpChartMap_of_mem_pow Z v.1 (a v ℓ) (n := 1)
      (x := X.presheaf.map (homOfLE v.2).op (c.x i))
      (by rw [pow_one]; exact c.restrict_mem_ideal v.1 v.2 i)
    refine ⟨w, ?_⟩
    rw [F1, F1, hw, pow_one, mul_comm]

/-- The *chart transform* `π⁻¹_{*,U_ℓ}(f, m) = (π^*f / x_ℓ^m, m)` of a marked function `(f, m)`
with `f ∈ 𝒪_X(U)`, with `π^*f / x_ℓ^m ∈ 𝒪_{U_ℓ}[x_ℓ^{-1}]` (Kollár (3.60.3)). -/
@[mmp "def_kr3c_chart_transform_marked_function"]
def chartTransform (ℓ : Fin c.r) (f : Γ(X, c.U)) (m : ℕ) :
    Localization.Away (c.chartPullback ℓ (c.x ℓ)) × ℕ :=
  (Localization.mk (c.chartPullback ℓ f) ⟨c.chartPullback ℓ (c.x ℓ) ^ m, m, rfl⟩, m)

end BlowupChartData

/-! ### Birational transforms -/

section Transform

variable {X : Scheme.{u}}

/-- The *ideal quotient* `(A : B)` of ideal sheaves: the largest quasi-coherent ideal sheaf whose
sections on every affine open `V` lie in `(A(V) : B(V))`. For an invertible `B` dividing `A`,
it is `B⁻¹·A`. -/
def idealColon (A B : X.IdealSheafData) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun V => Submodule.colon (A.ideal V) (B.ideal V : Set Γ(X, V))

/-- If `m ≤ ord I` in a local ring then `I ⊆ 𝔪^m`. -/
theorem le_pow_of_le_idealOrder {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} {m : ℕ}
    (h : (m : ℕ∞) ≤ idealOrder I) : I ≤ maximalIdeal R ^ m := by
  by_contra hne
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact hne (by simp)
  have : idealOrder I ≤ ((m - 1 : ℕ) : ℕ∞) := by
    refine iSup₂_le fun j hj => ?_
    have : j < m := by
      by_contra hjm
      exact hne (hj.trans (Ideal.pow_le_pow_right (by omega)))
    exact_mod_cast Nat.le_sub_one_of_lt this
  have : m ≤ m - 1 := by exact_mod_cast h.trans this
  omega

private theorem smooth_of_isSmoothScheme' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : MMP.Mori.IsSmoothScheme f) : Smooth f := by
  have hc : iSup (fun U : {U : X.Opens // Smooth (U.ι ≫ f)} => (U.1 : X.Opens)) = ⊤ := by
    rw [MMP.Mori.IsSmoothScheme, MMP.Mori.smoothLocus] at h
    rw [← h, sSup_eq_iSup']
    exact le_antisymm (iSup_le fun _ => le_iSup _ _) (iSup_le fun _ => le_iSup _ _)
  have : IsZariskiLocalAtSource @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth) _ hc]
  exact fun U => U.2

/-- The generic point of an irreducible component `W` of the support of `Z` is a generic point
of `W`. -/
theorem isGenericPoint_genericPoint_of_mem_componentsOf {Z : X.IdealSheafData} {W : Set X}
    (hW : W ∈ componentsOf (Z.support : Set X)) : IsGenericPoint hW.1.1.genericPoint W := by
  have hcl : closure W = W := Set.Subset.antisymm
    (hW.2 ⟨hW.1.1.closure, Z.support.2.closure_subset_iff.mpr hW.1.2⟩ subset_closure)
    subset_closure
  have := hW.1.1.isGenericPoint_genericPoint_closure
  rwa [hcl] at this

/-- The generic point of an irreducible component of the support of `Z` through `x` is a generic
point of a component of `Z` through `x`. -/
theorem genericPoint_mem_componentGenericPointsThrough {Z : X.IdealSheafData} {W : Set X}
    (hW : W ∈ componentsOf (Z.support : Set X)) {x : X} (hxW : x ∈ W) :
    hW.1.1.genericPoint ∈ Stacks.Chow.componentGenericPointsThrough Z x := by
  have hgen := isGenericPoint_genericPoint_of_mem_componentsOf hW
  refine ⟨hW.1.2 hgen.mem, hgen.specializes hxW, fun η' hη' hηw => ?_⟩
  have hsub : closure ({η'} : Set X) ⊆ (Z.support : Set X) :=
    Z.support.2.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη')
  have hWle : W ⊆ closure ({η'} : Set X) := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηw.mem_closure) isClosed_closure
  have hη'W : η' ∈ W := hW.2 ⟨isIrreducible_singleton.closure, hsub⟩ hWle (subset_closure rfl)
  rw [← hgen.def] at hη'W
  exact (hηw.antisymm (specializes_iff_mem_closure.mpr hη'W)).eq

/-- Local structure of the components of a smooth centre `Z` through a point `x` of `Z`: exactly
one irreducible component `W` of the support passes through `x`, its reduced ideal has the stalk
`stalk Z x` at `x`, and an ideal sheaf of order `≥ n` along `W` has its stalk at `x` inside
`(stalk Z x)^n`. -/
theorem exists_component_through {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (I : X.IdealSheafData) (x : X)
    (hx : x ∈ (Z.support : Set X)) :
    ∃ (W : Set X) (hW : W ∈ componentsOf (Z.support : Set X)), x ∈ W ∧
      (∀ W' ∈ componentsOf (Z.support : Set X), x ∈ W' → W' = W) ∧
      IdealSheafData.stalk (componentsFamily (Z.support : Set X) ⟨W, hW⟩) x =
        IdealSheafData.stalk Z x ∧
      ∀ n : ℕ, (n : ℕ∞) ≤ orderAlong I hW.1.1 →
        IdealSheafData.stalk I x ≤ IdealSheafData.stalk Z x ^ n := by
  have _ := smooth_of_isSmoothScheme' sX hX
  have hZs := smooth_of_isSmoothScheme' _ hZ
  have hR : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX x
  obtain ⟨y, hy⟩ : x ∈ Set.range Z.subschemeι := by rw [Z.range_subschemeι]; exact hx
  subst hy
  have hRy : IsRegularLocalRing (Z.subscheme.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_smooth_over_field (Z.subschemeι ≫ sX) y
  set J := IdealSheafData.stalk Z (Z.subschemeι y)
  have hJ : IsRegularLocalRing (X.presheaf.stalk (Z.subschemeι y) ⧸ J) := by
    have h1 := IsRegularLocalRing.of_ringEquiv (R := Z.subscheme.presheaf.stalk y)
      ((Z.subschemeι.stalkMap y).hom.quotientKerEquivOfSurjective
        (Z.subschemeι.stalkMap_surjective y)).symm
    rwa [Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk Z y] at h1
  have hprime : J.IsPrime := by
    haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk (Z.subschemeι y) ⧸ J)
    exact Ideal.Quotient.isDomain_iff_prime J |>.1 inferInstance
  let q : PrimeSpectrum (X.presheaf.stalk (Z.subschemeι y)) := ⟨J, hprime⟩
  have hmin : J ∈ J.minimalPrimes := ⟨⟨hprime, le_rfl⟩, fun p hp _ => hp.2⟩
  have hη := (Stacks.Chow.fromSpecStalk_mem_componentGenericPointsThrough_iff Z _ q).2 hmin
  set η := X.fromSpecStalk (Z.subschemeι y) q
  have hW := Stacks.Chow.maximal_isIrreducible_closure_of_mem_componentGenericPointsThrough hη
  refine ⟨closure {η}, hW, hη.2.1.mem_closure, ?_, ?_, ?_⟩
  · intro W' hW' hxW'
    have hgen := isGenericPoint_genericPoint_of_mem_componentsOf hW'
    obtain ⟨q', hq'min, hq'⟩ := (Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes Z _).surjOn
      (genericPoint_mem_componentGenericPointsThrough hW' hxW')
    have hqq : q'.asIdeal = J := le_antisymm (hq'min.2 ⟨hprime, le_rfl⟩ hq'min.1.2) hq'min.1.2
    rw [← hgen.def, ← hq', show q' = q from PrimeSpectrum.ext hqq]
  · have hcc : Closeds.closure (closure ({η} : Set X)) = Closeds.closure ({η} : Set X) :=
      Closeds.ext (by rw [Closeds.coe_closure, Closeds.coe_closure, closure_closure])
    change IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (closure ({η} : Set X)))) _ = _
    rw [hcc]
    exact Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk _ q
  · intro n hn
    have hg : (hW.1.1).genericPoint = η := by
      have h1 := hW.1.1.isGenericPoint_genericPoint_closure
      rw [closure_closure] at h1
      exact h1.eq (isGenericPoint_closure : IsGenericPoint η (closure {η}))
    have hmo : (n : ℕ∞) ≤ idealOrder (IdealSheafData.stalk I η) := by
      rwa [show orderAlong I hW.1.1 = multAt I η by rw [orderAlong, hg]] at hn
    have hle := le_pow_of_le_idealOrder hmo
    letI : Algebra (X.presheaf.stalk (Z.subschemeι y)) (X.presheaf.stalk η) :=
      (X.presheaf.stalkSpecializes hη.2.1).hom.toAlgebra
    haveI := Stacks.Chow.isLocalization_stalk_of_specializes hη.2.1 q rfl
    intro a ha
    have h1 : algebraMap _ (X.presheaf.stalk η) a ∈ IdealSheafData.stalk I η := by
      rw [Stacks.Chow.idealStalk_eq_map_stalkSpecializes I hη.2.1]
      exact Ideal.mem_map_of_mem _ ha
    have h2 := hle h1
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal J (X.presheaf.stalk η), ← Ideal.map_pow] at h2
    exact mem_pow_of_algebraMap_mem_map_pow J hJ (X.presheaf.stalk η) n h2

/-- At a point `x` of a smooth centre `Z`, in a smooth scheme, an ideal sheaf of order `≥ m` along
`Z` has stalk inside `(stalk Z x)^m`. -/
theorem stalk_le_pow_of_orderAlongGE {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (I : X.IdealSheafData) (m : ℕ)
    (hI : OrderAlongGE I (Z.support : Set X) m) (x : X) :
    IdealSheafData.stalk I x ≤ IdealSheafData.stalk Z x ^ m := by
  by_cases hx : x ∈ (Z.support : Set X)
  swap
  · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support Z x).2 hx]
    refine le_top.trans (le_of_eq ?_)
    rw [← Ideal.one_eq_top, one_pow]
  obtain ⟨W, hW, -, -, -, h⟩ := exists_component_through sX hX Z hZ I x hx
  exact h m (hI W hW)

/-- If the stalks of `I` lie in the `m`-th powers of the stalks of `Z` at every point, then the
pullback of `I` along `f` is contained in the `m`-th power of the pullback of `Z`. -/
theorem comap_le_comap_pow_of_stalk_le {Y : Scheme.{u}} (f : Y ⟶ X) (I Z : X.IdealSheafData) (m : ℕ)
    (h : ∀ x, IdealSheafData.stalk I x ≤ IdealSheafData.stalk Z x ^ m) :
    I.comap f ≤ Z.comap f ^ m := by
  refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
  rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_comap, IdealSheafData.stalk_comap,
    ← Ideal.map_pow]
  exact Ideal.map_mono (h _)

/-- The *birational transform* `π⁻¹_{Z*}(I, m) = (𝒪_{B_ZX}(mF)·π^*I, m)` of a marked ideal under
the blow-up `π : B_ZX → X`, `F = π⁻¹(Z)` (Kollár Def. 3.48 = Def. 3.60 (3.60.1)): the ideal
quotient `(π^*I : I_F^m)`. -/
@[mmp "def_kr3c_birational_transform_marked_ideal"]
def MarkedIdeal.birationalTransform (Z : X.IdealSheafData) (a : MarkedIdeal X) :
    MarkedIdeal (blowUp Z) :=
  ⟨idealColon (a.I.comap (blowUpToBase Z)) (Z.comap (blowUpToBase Z) ^ a.m), a.m⟩

theorem MarkedIdeal.birationalTransform_I (Z : X.IdealSheafData) (a : MarkedIdeal X) :
    (a.birationalTransform Z).I =
      idealColon (a.I.comap (blowUpToBase Z)) (Z.comap (blowUpToBase Z) ^ a.m) := rfl

@[simp] theorem MarkedIdeal.birationalTransform_m (Z : X.IdealSheafData) (a : MarkedIdeal X) :
    (a.birationalTransform Z).m = a.m := rfl

/-- For a smooth center `Z` of a smooth `X` whose components have codimension `≥ 1` and with
`ord_Z I ≥ m`, the birational transform is `𝒪(mF)·π^*I`: multiplied by `𝒪(-mF) = I_F^m` it
gives back `π^*I`. -/
@[mmp "def_kr3c_birational_transform_marked_ideal"]
theorem MarkedIdeal.birationalTransform_mul_eq {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (a : MarkedIdeal X)
    (ha : OrderAlongGE a.I (Z.support : Set X) a.m) :
    (a.birationalTransform Z).I * Z.comap (blowUpToBase Z) ^ a.m = a.I.comap (blowUpToBase Z) := by
  classical
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
  have hZa : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z) ^ a.m) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow hZc a.m
  have hle : a.I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ a.m :=
    comap_le_comap_pow_of_stalk_le _ _ _ _ (stalk_le_pow_of_orderAlongGE sX hX Z hZ a.I a.m ha)
  have hcol : idealColon (a.I.comap (blowUpToBase Z)) (Z.comap (blowUpToBase Z) ^ a.m) =
      Scheme.IdealSheafData.colon (a.I.comap (blowUpToBase Z)) (Z.comap (blowUpToBase Z) ^ a.m)
        (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor _ hZa) := by
    unfold idealColon
    exact Scheme.IdealSheafData.ofIdeals_ideal
      (Scheme.IdealSheafData.colon (a.I.comap (blowUpToBase Z)) (Z.comap (blowUpToBase Z) ^ a.m)
        (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor _ hZa))
  rw [MarkedIdeal.birationalTransform_I, hcol, mul_comm]
  exact AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor _ _ hZa hle

/-- The ideal `𝒪_{B_ZX}(-∑_j m_j F_j) = ∏_j I_{F_j}^{m_j}`, `F_j = π⁻¹(Z_j)` for the irreducible
components `Z_j` of `Z` with their reduced structure and `m_j = ord_{Z_j} I`. -/
def controlledTransformDivisorIdeal (Z : X.IdealSheafData) (I : X.IdealSheafData) :
    (blowUp Z).IdealSheafData :=
  ∏ᶠ W : componentsOf (Z.support : Set X),
    (componentsFamily (Z.support : Set X) W).comap (blowUpToBase Z) ^
      (orderAlong I W.2.1.1).toNat

/-- The *birational* (controlled, weak) *transform* `π⁻¹_{Z*}I = 𝒪_{B_ZX}(∑_j m_jF_j)·π^*I` of an
ideal sheaf along the blow-up of a smooth center `Z` with irreducible components `Z_j`,
`F_j = π⁻¹(Z_j)`, `m_j = ord_{Z_j} I` (Kollár 3.58 (3.58.1)). -/
@[mmp "def_kr3c_birational_transform_ideal_smooth_blowup"]
def controlledTransform (Z : X.IdealSheafData) (I : X.IdealSheafData) :
    (blowUp Z).IdealSheafData :=
  idealColon (I.comap (blowUpToBase Z)) (controlledTransformDivisorIdeal Z I)

/-- The stalk of the unit ideal sheaf is the whole local ring. -/
theorem stalk_one (x : X) : IdealSheafData.stalk (1 : X.IdealSheafData) x = ⊤ := by
  rw [IdealSheafData.stalk_eq_top_iff_notMem_support]
  exact fun h => h

/-- The stalk of a finite product of ideal sheaves is the product of their stalks. -/
theorem stalk_prod {ι : Type*} (s : Finset ι) (f : ι → X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (∏ i ∈ s, f i) x = ∏ i ∈ s, IdealSheafData.stalk (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using stalk_one x
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, IdealSheafData.stalk_mul, ih]

/-- A closed subset of a Noetherian space has finitely many irreducible components. -/
theorem finite_componentsOf {T : Type*} [TopologicalSpace T] [NoetherianSpace T] {D : Set T}
    (hD : IsClosed D) : (componentsOf D).Finite := by
  obtain ⟨𝒮, h𝒮fin, h𝒮closed, h𝒮irr, h𝒮cover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hD
  lift 𝒮 to Finset (Set T) using h𝒮fin
  refine 𝒮.finite_toSet.subset fun W hW => ?_
  have hsub : W ⊆ ⋃₀ 𝒮 := h𝒮cover ▸ hW.1.2
  obtain ⟨t, ht, hWt⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hW.1.1 𝒮 (fun s hs => h𝒮closed s hs) hsub
  have htW : t ⊆ W := hW.2 ⟨h𝒮irr t ht, h𝒮cover ▸ Set.subset_sUnion_of_mem ht⟩ hWt
  rw [Set.Subset.antisymm hWt htW]; exact ht

/-- Every irreducible component of a closed subset is closed. -/
theorem isClosed_of_mem_componentsOf {T : Type*} [TopologicalSpace T] {D : Set T}
    (hD : IsClosed D) {W : Set T}
    (hW : W ∈ componentsOf D) : IsClosed W := by
  have hcl : closure W ⊆ W := hW.2 ⟨hW.1.1.closure, hD.closure_subset_iff.mpr hW.1.2⟩ subset_closure
  exact closure_subset_iff_isClosed.mp hcl

/-- At a point outside an irreducible component `W` of `Z`, the stalk of the reduced ideal sheaf of
`W` is the whole local ring. -/
theorem stalk_componentsFamily_eq_top (Z : X.IdealSheafData) {W : Set X}
    (hW : W ∈ componentsOf (Z.support : Set X)) {x : X} (hx : x ∉ W) :
    IdealSheafData.stalk (componentsFamily (Z.support : Set X) ⟨W, hW⟩) x = ⊤ := by
  rw [IdealSheafData.stalk_eq_top_iff_notMem_support]
  intro h
  have h2 : x ∈ ((componentsFamily (Z.support : Set X) ⟨W, hW⟩).support : Set X) := h
  change x ∈ ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure W)).support : Set X) at h2
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure] at h2
  exact hx ((isClosed_of_mem_componentsOf Z.support.2 hW).closure_eq ▸ h2)

/-- For a smooth centre `Z` in a smooth scheme `X` of finite type over `k` and a point `y` of the
blow-up `π : B_ZX → X`, there is `n` such that the stalk at `y` of
`controlledTransformDivisorIdeal Z I` is the `n`-th power of the stalk of `π^*I_Z`, and the stalk
of `I` at `π y` lies in the `n`-th power of the stalk of `I_Z`. -/
theorem exists_stalk_divisor_eq {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (y : blowUp Z) :
    ∃ n : ℕ, IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
        IdealSheafData.stalk (Z.comap (blowUpToBase Z)) y ^ n ∧
      IdealSheafData.stalk I (blowUpToBase Z y) ≤
        IdealSheafData.stalk Z (blowUpToBase Z y) ^ n := by
  classical
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  haveI : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  letI := Fintype.ofFinite (componentsOf (Z.support : Set X))
  set x := blowUpToBase Z y with hxdef
  have hfac : ∀ W : componentsOf (Z.support : Set X),
      IdealSheafData.stalk ((componentsFamily (Z.support : Set X) W).comap (blowUpToBase Z) ^
        (orderAlong I W.2.1.1).toNat) y =
      Ideal.map ((blowUpToBase Z).stalkMap y).hom
        (IdealSheafData.stalk (componentsFamily (Z.support : Set X) W) x) ^
          (orderAlong I W.2.1.1).toNat := by
    intro W
    rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
  have hD : IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
      ∏ W : componentsOf (Z.support : Set X), Ideal.map ((blowUpToBase Z).stalkMap y).hom
        (IdealSheafData.stalk (componentsFamily (Z.support : Set X) W) x) ^
          (orderAlong I W.2.1.1).toNat := by
    unfold controlledTransformDivisorIdeal
    rw [finprod_eq_prod_of_fintype, stalk_prod]
    exact Finset.prod_congr rfl fun W _ => hfac W
  by_cases hx : x ∈ (Z.support : Set X)
  · obtain ⟨W0, hW0, hxW0, huniq, hstalk, hle⟩ := exists_component_through sX hX Z hZ I x hx
    refine ⟨(orderAlong I hW0.1.1).toNat, ?_, hle _ (ENat.coe_toNat_le_self _)⟩
    rw [hD, Finset.prod_eq_single (⟨W0, hW0⟩ : componentsOf (Z.support : Set X))]
    · rw [hstalk, ← IdealSheafData.stalk_comap]
    · intro W _ hne
      have : x ∉ (W : Set X) := fun hxW => hne (Subtype.ext (huniq W W.2 hxW))
      rw [stalk_componentsFamily_eq_top Z W.2 this, Ideal.map_top, ← Ideal.one_eq_top, one_pow]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine ⟨0, ?_, ?_⟩
    · rw [pow_zero, hD]
      refine Finset.prod_eq_one fun W _ => ?_
      have : x ∉ (W : Set X) := fun hxW => hx (W.2.1.2 hxW)
      rw [stalk_componentsFamily_eq_top Z W.2 this, Ideal.map_top, ← Ideal.one_eq_top, one_pow]
    · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support Z x).2 hx]
      rw [pow_zero, Ideal.one_eq_top]; exact le_top

/-- For a smooth center `Z` of a smooth `X` whose components have codimension `≥ 1`, and `I`
nonzero on every irreducible component of `X`, the controlled transform is
`𝒪(∑_j m_jF_j)·π^*I`: multiplied by `𝒪(-∑_j m_jF_j)` it gives back `π^*I`. -/
@[mmp "def_kr3c_birational_transform_ideal_smooth_blowup"]
theorem controlledTransform_mul_eq {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (I : X.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) :
    controlledTransform Z I * controlledTransformDivisorIdeal Z I =
      I.comap (blowUpToBase Z) := by
  classical
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsLocallyNoetherian (blowUp Z) :=
    AlgebraicGeometry.TwoStepTower.isLocallyNoetherian_blowUp
      (AlgebraicGeometry.TwoStepTower.isFiniteType_of_isLocallyNoetherian Z)
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
  have hDc : Stacks.Divisors.IsEffectiveCartierDivisor (controlledTransformDivisorIdeal Z I) := by
    refine AlgebraicGeometry.isEffectiveCartierDivisor_of_stalk_regular_principal _ fun y _ => ?_
    obtain ⟨n, hn, -⟩ := exists_stalk_divisor_eq sX hX Z hZ I y
    obtain ⟨g, hg, hgs⟩ :=
      AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hZc y
    refine ⟨g ^ n, IsRegular.pow n hg, ?_⟩
    rw [hn, hgs, Ideal.span_singleton_pow]
  have hle : I.comap (blowUpToBase Z) ≤ controlledTransformDivisorIdeal Z I := by
    refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
    obtain ⟨n, hn, hle⟩ := exists_stalk_divisor_eq sX hX Z hZ I y
    rw [hn, IdealSheafData.stalk_comap, IdealSheafData.stalk_comap, ← Ideal.map_pow]
    exact Ideal.map_mono hle
  have hcol : controlledTransform Z I =
      Scheme.IdealSheafData.colon (I.comap (blowUpToBase Z)) (controlledTransformDivisorIdeal Z I)
        (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor _ hDc) := by
    unfold controlledTransform idealColon
    exact Scheme.IdealSheafData.ofIdeals_ideal
      (Scheme.IdealSheafData.colon (I.comap (blowUpToBase Z)) (controlledTransformDivisorIdeal Z I)
        (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor _ hDc))
  rw [hcol, mul_comm]
  exact AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor _ _ hDc hle

end Transform

/-! ### The divisorial part -/

section DivisorialPart

variable {X : Scheme.{u}}

open Classical in
/-- The coefficient `ord_D(I)` of a prime divisor `D` in `Div(I)`: nonzero only if `D` is an
irreducible component of `cosupp I` (necessarily of codimension one). -/
@[mmp "def_kr3c_divisorial_part"]
def divisorialPartCoeff (I : X.IdealSheafData) (D : AlgebraicGeometry.PrimeDivisor X) : ℤ :=
  if (D.support : Set X) ∈ componentsOf (I.support : Set X) then
    ((multAt I D.genericPoint).toNat : ℤ)
  else 0

open Classical in
/-- The *divisorial part divisor* `Div(I) = ∑_D ord_D(I)·D` over the irreducible components `D`
of `cosupp I` of codimension one in `X` (Kollár Def. 3.48), a finite sum on a noetherian `X`
(`0` if there were infinitely many such components). -/
@[mmp "def_kr3c_divisorial_part"]
def divisorialPart (I : X.IdealSheafData) : MMP.Mori.Divisor X :=
  if h : (Function.support (divisorialPartCoeff I)).Finite then
    Finsupp.ofSupportFinite _ h
  else 0

/-- On a noetherian scheme the sum defining `Div(I)` is finite. -/
@[mmp "def_kr3c_divisorial_part"]
theorem finite_support_divisorialPartCoeff [IsNoetherian X] (I : X.IdealSheafData) :
    (Function.support (divisorialPartCoeff I)).Finite := by
  refine Set.Finite.of_finite_image (f := fun D : AlgebraicGeometry.PrimeDivisor X => D.support)
    ((finite_componentsOf I.support.isClosed).subset ?_) ?_
  · rintro - ⟨D, hD, rfl⟩
    by_contra h
    exact hD (by simp [divisorialPartCoeff, h])
  · intro a _ b _ hab
    have ha := AlgebraicGeometry.PrimeDivisor.support_eq_closure a
    have hb := AlgebraicGeometry.PrimeDivisor.support_eq_closure b
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    have hab' : a.support = b.support := hab
    have : IsGenericPoint a.genericPoint (closure ({b.genericPoint} : Set X)) := by
      rw [← hb, ← hab', ha]; exact isGenericPoint_closure
    exact this.eq isGenericPoint_closure

/-- The *divisorial part* `𝒪_X(-Div(I)) = ∏_D I_D^{ord_D I}` of `I` (Kollár Def. 3.48). -/
@[mmp "def_kr3c_divisorial_part"]
def divisorialPartIdeal (I : X.IdealSheafData) : X.IdealSheafData :=
  ∏ᶠ D : AlgebraicGeometry.PrimeDivisor X, D.idealSheaf ^ (divisorialPartCoeff I D).toNat

end DivisorialPart

/-! ### Completions and fields of representatives -/

/-- The *completion* `X̂_x = Spec 𝒪̂_{x,X}` of a scheme `X` at a point `x` (Kollár Def. 3.55),
`𝒪̂_{x,X} = lim 𝒪_{x,X}/𝔪_x^s`. -/
@[mmp "def_kr3c_completion_at_point"]
def completionAtPoint (X : Scheme.{u}) (x : X) : Scheme.{u} :=
  Spec (.of (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))

/-- The canonical morphism `X̂_x → Spec 𝒪_{x,X} → X`. -/
@[mmp "def_kr3c_completion_at_point"]
def completionAtPointToScheme (X : Scheme.{u}) (x : X) : completionAtPoint X x ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))) ≫
    X.fromSpecStalk x

/-- The structure morphism `X̂_x → X → Spec k` making `X̂_x` a `k`-scheme. -/
@[mmp "def_kr3c_completion_at_point"]
def completionAtPointStructure {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (x : X) : completionAtPoint X x ⟶ Spec (.of k) :=
  completionAtPointToScheme X x ≫ sX

/-- A *field of representatives* (coefficient field) of a local ring `(R, 𝔪)` (Kollár
Def. 3.55): a subring `k' ⊆ R` which is a field and maps isomorphically onto `R/𝔪` under the
residue map. -/
@[mmp "def_kr3c_field_of_representatives"]
def IsFieldOfRepresentatives {R : Type*} [CommRing R] [IsLocalRing R] (K : Subring R) : Prop :=
  IsField K ∧ Function.Bijective ((residue R).comp K.subtype)

end MMP.Resolution
