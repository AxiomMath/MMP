module

public import MMP.Attr
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import MMP.AlgebraicGeometry.Curves.Maps.TwoStageObstruction
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Deformations of a map from a curve along small extensions: derivations, Čech obstructions

Let `f : C → U` be a map from a curve to a smooth variety, `A' → A` a small extension of local
Artinian `k`-algebras with kernel `J`, and `C_A → U` a map extending `f`. On an affine chart
`Spec R` of `C` (mapping into an affine chart `Spec S` of `U`, `S` formally smooth over `k`) the
maps `Spec (R ⊗ A') → U` lifting a given map `S → R ⊗ A` form a torsor under the derivations
`S → J ⊗ R` along it; maps that must also take prescribed values on the marked points `B` are
the lifts across the ideal `J ⊗ 𝔟`, and the derivations take values in `J ⊗ 𝔟`. Over a cover
these torsors glue to a Čech torsor, whose class in `Ȟ¹` is the first obstruction; the ratios of
the transition functions of two line bundles that agree over `A` are `1 + u_ij`, `u_ij ∈ J ⊗ R_ij`,
a Čech cocycle, whose class is the second obstruction.

## Main definitions

* `MMP.Fourfold.LiftsOf`, `MMP.Fourfold.Deriv`: the lifts of `φ : S → P/I` to `P` (`I` square-zero)
  and the derivations `S → I` along `φ`; `LiftsOf.sub`, `LiftsOf.add`: the torsor structure.
* `MMP.Fourfold.CechPresheaf`, `MMP.Fourfold.CechPresheaf.H1`: a presheaf of `k`-modules on the
  nerve of a finite cover and its first Čech cohomology (cocycles modulo coboundaries).
* `MMP.Fourfold.CechTorsor`, `MMP.Fourfold.CechTorsor.obstruction`: presheaves of pseudo-torsors
  and the obstruction class of a family of local objects.
* `MMP.Fourfold.LiftCover`: a lifting problem over a cover (rings `P_s`, square-zero ideals `I_s`,
  maps `φ_s : S → P_s / I_s`), with `LiftCover.derivPresheaf`, `LiftCover.liftTorsor`,
  `LiftCover.firstObstruction`, `LiftCover.secondObstruction`, and morphisms `LiftCover.Hom`
  (e.g. quotients of `J`).
* `MMP.Fourfold.firstOrderLiftEquiv`: first-order deformations are derivations.
* `MMP.Fourfold.ChartData`, `MMP.Fourfold.ChartedLiftCover`: the multi-chart version, with target
  charts `Spec (S s)` varying with the intersection `U_s` and formally étale chart maps; lifts and
  derivations restrict through the common chart (`MMP.Fourfold.ChartHom.extLift`,
  `MMP.Fourfold.ChartHom.extDeriv`), with `firstObstruction`, naturality, and the second
  obstruction through `toLiftCover`.
* `MMP.Fourfold.ChartedLiftCover.Compat`, `MMP.Fourfold.ChartedLiftCover.exists_glue`: compatible
  families of local lifts and their gluing to a morphism of schemes.
* `MMP.Fourfold.CurveDeformationData`,
  `MMP.Fourfold.CurveDeformationData.toTheory`: the two-stage obstruction theory attached to the
  Čech data of a family of curve maps.

## Main results

* `MMP.Fourfold.LiftsOf.nonempty`, `MMP.Fourfold.exists_lift_agreeing`: smooth lifting, also across
  `C_A ∪ B_{A'}` (the ideal `K ⊓ N`, square-zero by
  `MMP.Fourfold.inf_mul_inf_eq_bot_of_mul_eq_bot`); `MMP.Fourfold.mk_inf_comp_eq_iff`.
* `MMP.Fourfold.CechTorsor.obstruction_eq`, `MMP.Fourfold.CechTorsor.obstruction_eq_zero_iff`: the
  obstruction class is independent of the local objects, and vanishes iff they can be modified to
  glue.
* `MMP.Fourfold.LiftCover.firstObstruction_eq_zero_iff`: the first obstruction.
* `MMP.Fourfold.LiftCover.exists_iso_of_secondObstruction_eq_zero`,
  `MMP.Fourfold.LiftCover.secondObstruction_eq_zero_of_iso`,
  `MMP.Fourfold.LiftCover.secondObstruction_eq_zero_iff`: the second obstruction vanishes iff
  the transition functions are isomorphic over the identity modulo the ideals.
* `MMP.Fourfold.CechTorsor.Hom.obstruction_map`, `MMP.Fourfold.LiftCover.Hom.firstObstruction_map`,
  `MMP.Fourfold.LiftCover.Hom.secondObstruction_map`: naturality of both obstructions.
* `MMP.Fourfold.SmallExtension.ker_tensor_mul_ker`: `ker (R ⊗ B → R ⊗ A)` is square-zero.
* `MMP.Fourfold.snd_mem_iff_fixed`: first-order maps fixing the marked points are the derivations
  with values in the ideal of the marked points.

## Implementation notes

`H¹` is Čech cohomology of the presheaf on the finite cover (all ordered pairs and triples of
indices). Intersections `U_s` are indexed by `Finset ι`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace MMP.Fourfold

universe u v w

section SquareZero

variable {k S P : Type*} [CommRing k] [CommRing S] [CommRing P] [Algebra k S] [Algebra k P]
  (I : Ideal P)

/-- In a square-zero ideal `I`, the product of two elements of `I` vanishes. -/
theorem mul_eq_zero_of_mem_of_mul_eq_bot (hI : I * I = ⊥) {x y : P} (hx : x ∈ I) (hy : y ∈ I) :
    x * y = 0 := by
  have : x * y ∈ I * I := Ideal.mul_mem_mul hx hy
  rwa [hI, Ideal.mem_bot] at this

/-- The lifts of `φ : S → P/I` to `P`. -/
abbrev LiftsOf (φ : S →ₐ[k] P ⧸ I) : Type _ :=
  {g : S →ₐ[k] P // (Ideal.Quotient.mkₐ k I).comp g = φ}

/-- The `k`-linear maps `S → I` satisfying the Leibniz rule along `φ`. -/
def derivs (φ : S →ₐ[k] P ⧸ I) : Submodule k (S →ₗ[k] I) where
  carrier := {D | ∀ (a b : S) (p q : P), Ideal.Quotient.mk I p = φ a → Ideal.Quotient.mk I q = φ b →
    ((D (a * b) : I) : P) = p * D b + q * D a}
  zero_mem' := by intro a b p q _ _; simp
  add_mem' := by
    intro D₁ D₂ h₁ h₂ a b p q hp hq
    simp only [LinearMap.add_apply, Submodule.coe_add, h₁ a b p q hp hq, h₂ a b p q hp hq]
    ring
  smul_mem' := by
    intro c D h a b p q hp hq
    simp only [LinearMap.smul_apply, Submodule.coe_smul_of_tower, h a b p q hp hq, smul_add,
      mul_smul_comm]

variable {I}

/-- The derivations along `φ` with values in `I`, as a type. -/
abbrev Deriv (I : Ideal P) (φ : S →ₐ[k] P ⧸ I) : Type _ := ↥(derivs I φ)

/-- The Leibniz rule `D (a b) = p · D b + q · D a` for any representatives `p`, `q` of `φ a`,
`φ b`. -/
theorem Deriv.leibniz {φ : S →ₐ[k] P ⧸ I} (D : Deriv I φ) (a b : S) (p q : P)
    (hp : Ideal.Quotient.mk I p = φ a) (hq : Ideal.Quotient.mk I q = φ b) :
    ((D.1 (a * b) : I) : P) = p * D.1 b + q * D.1 a := D.2 a b p q hp hq

/-- Two lifts of `φ` agree modulo `I`. -/
theorem LiftsOf.sub_mem {φ : S →ₐ[k] P ⧸ I} (g₁ g₂ : LiftsOf I φ) (a : S) :
    g₁.1 a - g₂.1 a ∈ I := by
  rw [← Ideal.Quotient.eq]
  simpa using congr($(g₁.2.trans g₂.2.symm) a)

/-- A lift `g` of `φ` satisfies `g a ≡ φ a` modulo `I`. -/
theorem LiftsOf.mk_apply {φ : S →ₐ[k] P ⧸ I} (g : LiftsOf I φ) (a : S) :
    Ideal.Quotient.mk I (g.1 a) = φ a := by
  simpa using congr($(g.2) a)

/-- The difference of two lifts of `φ` is a derivation along `φ` with values in `I`. -/
def LiftsOf.sub (hI : I * I = ⊥) {φ : S →ₐ[k] P ⧸ I} (g₁ g₂ : LiftsOf I φ) : Deriv I φ :=
  ⟨diffToIdealOfQuotientCompEq I g₁.1 g₂.1 (g₁.2.trans g₂.2.symm), by
    intro a b p q hp hq
    have hpa : p - g₂.1 a ∈ I := Ideal.Quotient.eq.1 (by rw [hp, g₂.mk_apply])
    have hqb : q - g₂.1 b ∈ I := Ideal.Quotient.eq.1 (by rw [hq, g₂.mk_apply])
    have z1 := mul_eq_zero_of_mem_of_mul_eq_bot I hI hpa (g₁.sub_mem g₂ b)
    have z2 := mul_eq_zero_of_mem_of_mul_eq_bot I hI hqb (g₁.sub_mem g₂ a)
    have z3 := mul_eq_zero_of_mem_of_mul_eq_bot I hI (g₁.sub_mem g₂ a) (g₁.sub_mem g₂ b)
    simp only [diffToIdealOfQuotientCompEq_apply, map_mul]
    linear_combination z3 - z1 - z2⟩

/-- The derivation `g₁ - g₂` sends `a` to `g₁ a - g₂ a`. -/
@[simp] theorem LiftsOf.sub_apply (hI : I * I = ⊥) {φ : S →ₐ[k] P ⧸ I} (g₁ g₂ : LiftsOf I φ)
    (a : S) : (((g₁.sub hI g₂).1 a : I) : P) = g₁.1 a - g₂.1 a := by
  simp [LiftsOf.sub]

/-- A derivation along `φ` vanishes on `1`. -/
theorem Deriv.map_one {φ : S →ₐ[k] P ⧸ I} (D : Deriv I φ) : D.1 1 = 0 := by
  have h := D.leibniz 1 1 1 1 (by simp) (by simp)
  simp only [mul_one, one_mul] at h
  apply Subtype.ext
  have : ((D.1 1 : I) : P) = 0 := by linear_combination (-1 : P) * h
  simpa using this

/-- A derivation along `φ` vanishes on the image of `k`. -/
theorem Deriv.map_algebraMap {φ : S →ₐ[k] P ⧸ I} (D : Deriv I φ) (r : k) :
    D.1 (algebraMap k S r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, D.map_one, smul_zero]

/-- The algebra homomorphism `g + D`, for `g` a lift of `φ` and `D` a derivation along `φ`. -/
def LiftsOf.addAlgHom (hI : I * I = ⊥) {φ : S →ₐ[k] P ⧸ I} (g : LiftsOf I φ) (D : Deriv I φ) :
    S →ₐ[k] P where
  toFun := fun a => g.1 a + (D.1 a : P)
  map_one' := by simp [D.map_one]
  map_mul' := by
    intro a b
    have h := D.leibniz a b (g.1 a) (g.1 b) (g.mk_apply a) (g.mk_apply b)
    have z := mul_eq_zero_of_mem_of_mul_eq_bot I hI (D.1 a).2 (D.1 b).2
    rw [map_mul, h]
    linear_combination (-1 : P) * z
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, Submodule.coe_add]
    ring
  commutes' := by intro r; simp [D.map_algebraMap]

/-- Translating a lift of `φ` by a derivation along `φ`. -/
def LiftsOf.add (hI : I * I = ⊥) {φ : S →ₐ[k] P ⧸ I} (g : LiftsOf I φ) (D : Deriv I φ) :
    LiftsOf I φ :=
  ⟨g.addAlgHom hI D, by
    ext a
    simp [LiftsOf.addAlgHom, Ideal.Quotient.eq_zero_iff_mem.2 (D.1 a).2, g.mk_apply]⟩

/-- The lift `g + D` sends `a` to `g a + D a`. -/
@[simp] theorem LiftsOf.add_apply (hI : I * I = ⊥) {φ : S →ₐ[k] P ⧸ I} (g : LiftsOf I φ)
    (D : Deriv I φ) (a : S) : (g.add hI D).1 a = g.1 a + (D.1 a : P) := rfl

/-- Translating `g₂` by `g₁ - g₂` gives `g₁`. -/
theorem LiftsOf.sub_add_cancel (hI : I * I = ⊥) {φ : S →ₐ[k] P ⧸ I} (g₁ g₂ : LiftsOf I φ) :
    g₂.add hI (g₁.sub hI g₂) = g₁ := by
  apply Subtype.ext; ext a; simp

/-- The difference `(g + D) - g` is `D`. -/
theorem LiftsOf.add_sub_cancel (hI : I * I = ⊥) {φ : S →ₐ[k] P ⧸ I} (g : LiftsOf I φ)
    (D : Deriv I φ) : (g.add hI D).sub hI g = D := by
  apply Subtype.ext; ext a; simp

/-- Translating by `D` and then by `E` is translating by `D + E`. -/
theorem LiftsOf.add_add (hI : I * I = ⊥) {φ : S →ₐ[k] P ⧸ I} (g : LiftsOf I φ)
    (D E : Deriv I φ) : (g.add hI D).add hI E = g.add hI (D + E) := by
  apply Subtype.ext; ext a; simp [add_assoc]

/-- Translating a lift by the zero derivation leaves it unchanged. -/
theorem LiftsOf.add_zero (hI : I * I = ⊥) {φ : S →ₐ[k] P ⧸ I} (g : LiftsOf I φ) :
    g.add hI 0 = g := by
  apply Subtype.ext; ext a; simp

/-- A square-zero ideal is nilpotent. -/
theorem isNilpotent_of_mul_eq_bot (hI : I * I = ⊥) : IsNilpotent I :=
  ⟨2, (pow_two I).trans hI⟩

/-- **Smooth lifting along a square-zero thickening** (Mathlib's `FormallySmooth.lift`): the lifts
of a map `S → P/I` from a formally smooth `k`-algebra `S` exist. -/
theorem LiftsOf.nonempty [Algebra.FormallySmooth k S] (hI : I * I = ⊥) (φ : S →ₐ[k] P ⧸ I) :
    Nonempty (LiftsOf I φ) :=
  ⟨⟨Algebra.FormallySmooth.lift I (isNilpotent_of_mul_eq_bot hI) φ,
    Algebra.FormallySmooth.comp_lift I (isNilpotent_of_mul_eq_bot hI) φ⟩⟩

/-- **Lifting across a union**: let `K`, `N` be ideals of `P` with `(K ⊓ N)² = 0` (in the
application `P = 𝒪(C_{A'})`-chart, `K = J·P` the ideal of `C_A` and `N = 𝔟·P` the ideal of the
marked points `B_{A'}`, so `K ⊓ N = J ⊗ 𝔟`).  A map `φ : S → P/K` and a map `ψ : S → P/N` that
agree on `P/(K ⊔ N)` (values on `B_A`) have a common lift `S → P`, for `S` formally smooth. -/
theorem exists_lift_agreeing [Algebra.FormallySmooth k S] (K N : Ideal P)
    (hKN : (K ⊓ N) * (K ⊓ N) = ⊥) (φ : S →ₐ[k] P ⧸ K) (ψ : S →ₐ[k] P ⧸ N)
    (hagree : ∀ (a : S) (x y : P), Ideal.Quotient.mk K x = φ a → Ideal.Quotient.mk N y = ψ a →
      x - y ∈ K ⊔ N) :
    ∃ g : S →ₐ[k] P, (Ideal.Quotient.mkₐ k K).comp g = φ ∧ (Ideal.Quotient.mkₐ k N).comp g = ψ := by
  let e : P →ₐ[k] (P ⧸ K) × (P ⧸ N) :=
    (Ideal.Quotient.mkₐ k K).prod (Ideal.Quotient.mkₐ k N)
  have hmem : ∀ a : S, (φ a, ψ a) ∈ e.range := by
    intro a
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ a)
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (ψ a)
    obtain ⟨κ, hκ, ν, hν, hsum⟩ := Submodule.mem_sup.1 (hagree a x y hx hy)
    refine ⟨x - κ, Prod.ext ?_ ?_⟩
    · change Ideal.Quotient.mk K (x - κ) = φ a
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hκ, sub_zero, hx]
    · change Ideal.Quotient.mk N (x - κ) = ψ a
      rw [show x - κ = y + ν by linear_combination (-1 : P) * hsum, map_add,
        Ideal.Quotient.eq_zero_iff_mem.2 hν, add_zero, hy]
  let f : S →ₐ[k] e.range := (φ.prod ψ).codRestrict e.range hmem
  have hker : IsNilpotent (RingHom.ker (e.rangeRestrict : P →+* e.range)) := by
    have : RingHom.ker (e.rangeRestrict : P →+* e.range) = K ⊓ N := by
      ext x
      simp [RingHom.mem_ker, e, Subtype.ext_iff, Ideal.Quotient.eq_zero_iff_mem, Prod.ext_iff]
    rw [this]
    exact isNilpotent_of_mul_eq_bot hKN
  have hl a := congrArg Subtype.val (Algebra.FormallySmooth.liftOfSurjective_apply f
    e.rangeRestrict e.rangeRestrict_surjective hker a)
  exact ⟨_, AlgHom.ext fun a => congrArg Prod.fst (hl a),
    AlgHom.ext fun a => congrArg Prod.snd (hl a)⟩

/-- Lifts of `χ = (g mod K ⊓ N)` through `P → P/(K ⊓ N)` are exactly the lifts that agree with `g`
modulo `K` and modulo `N`: the "fixed values" condition is the lifting problem along the ideal
`K ⊓ N`, in the application `J ⊗ 𝔟`. -/
theorem mk_inf_comp_eq_iff (K N : Ideal P) (g g' : S →ₐ[k] P) :
    (Ideal.Quotient.mkₐ k (K ⊓ N)).comp g' = (Ideal.Quotient.mkₐ k (K ⊓ N)).comp g ↔
      (Ideal.Quotient.mkₐ k K).comp g' = (Ideal.Quotient.mkₐ k K).comp g ∧
      (Ideal.Quotient.mkₐ k N).comp g' = (Ideal.Quotient.mkₐ k N).comp g := by
  have key : ∀ (J : Ideal P) (a : S),
      ((Ideal.Quotient.mkₐ k J).comp g') a = ((Ideal.Quotient.mkₐ k J).comp g) a ↔
        g' a - g a ∈ J := fun J a => by
    simp [Ideal.Quotient.eq]
  simp only [AlgHom.ext_iff, key, Ideal.mem_inf, forall_and]

end SquareZero

section Functoriality

variable {k S P P' : Type*} [CommRing k] [CommRing S] [CommRing P] [CommRing P'] [Algebra k S]
  [Algebra k P] [Algebra k P'] {I : Ideal P} {I' : Ideal P'} {φ : S →ₐ[k] P ⧸ I}
  {φ' : S →ₐ[k] P' ⧸ I'}

/-- A morphism of square-zero thickening problems over `S`: an algebra map `ψ : P → P'` sending
`I` into `I'` and carrying `φ` to `φ'` modulo the ideals. -/
structure SqZeroHom (I : Ideal P) (φ : S →ₐ[k] P ⧸ I) (I' : Ideal P') (φ' : S →ₐ[k] P' ⧸ I') where
  /-- The underlying algebra map. -/
  ψ : P →ₐ[k] P'
  mem : ∀ x ∈ I, ψ x ∈ I'
  compat : ∀ (a : S) (p : P), Ideal.Quotient.mk I p = φ a → Ideal.Quotient.mk I' (ψ p) = φ' a

namespace SqZeroHom

variable (h : SqZeroHom I φ I' φ')

/-- The image of a lift. -/
def mapLift (g : LiftsOf I φ) : LiftsOf I' φ' :=
  ⟨h.ψ.comp g.1, by ext a; exact h.compat a (g.1 a) (g.mk_apply a)⟩

/-- The image of a lift `g` sends `a` to `ψ (g a)`. -/
@[simp] theorem mapLift_apply (g : LiftsOf I φ) (a : S) : (h.mapLift g).1 a = h.ψ (g.1 a) := rfl

/-- The image of a derivation (with `I'` square zero). -/
def mapDeriv (hI' : I' * I' = ⊥) (D : Deriv I φ) : Deriv I' φ' :=
  ⟨{ toFun := fun a => ⟨h.ψ (D.1 a), h.mem _ (D.1 a).2⟩
     map_add' := by intro a b; apply Subtype.ext; simp
     map_smul' := by intro c a; apply Subtype.ext; simp }, by
    intro a b p' q' hp hq
    obtain ⟨p, hp0⟩ := Ideal.Quotient.mk_surjective (φ a)
    obtain ⟨q, hq0⟩ := Ideal.Quotient.mk_surjective (φ b)
    have hpp : h.ψ p - p' ∈ I' := Ideal.Quotient.eq.1 (by rw [h.compat a p hp0, hp])
    have hqq : h.ψ q - q' ∈ I' := Ideal.Quotient.eq.1 (by rw [h.compat b q hq0, hq])
    have z1 := mul_eq_zero_of_mem_of_mul_eq_bot I' hI' hpp (h.mem _ (D.1 b).2)
    have z2 := mul_eq_zero_of_mem_of_mul_eq_bot I' hI' hqq (h.mem _ (D.1 a).2)
    change h.ψ ((D.1 (a * b) : I) : P) = p' * h.ψ (D.1 b) + q' * h.ψ (D.1 a)
    rw [D.leibniz a b p q hp0 hq0, map_add, map_mul, map_mul]
    linear_combination z1 + z2⟩

/-- The image of a derivation `D` sends `a` to `ψ (D a)`. -/
@[simp] theorem mapDeriv_apply (hI' : I' * I' = ⊥) (D : Deriv I φ) (a : S) :
    (((h.mapDeriv hI' D).1 a : I') : P') = h.ψ (D.1 a) := rfl

/-- The image of `g + D` is the image of `g` translated by the image of `D`. -/
theorem mapLift_add (hI : I * I = ⊥) (hI' : I' * I' = ⊥) (g : LiftsOf I φ) (D : Deriv I φ) :
    h.mapLift (g.add hI D) = (h.mapLift g).add hI' (h.mapDeriv hI' D) := by
  apply Subtype.ext; ext a; simp

/-- The image of the difference `g₁ - g₂` is the difference of the images. -/
theorem mapDeriv_sub (hI : I * I = ⊥) (hI' : I' * I' = ⊥) (g₁ g₂ : LiftsOf I φ) :
    h.mapDeriv hI' (g₁.sub hI g₂) = (h.mapLift g₁).sub hI' (h.mapLift g₂) := by
  apply Subtype.ext; ext a; simp

/-- Compatibility of `mapDeriv` with addition. -/
theorem mapDeriv_add (hI' : I' * I' = ⊥) (D E : Deriv I φ) :
    h.mapDeriv hI' (D + E) = h.mapDeriv hI' D + h.mapDeriv hI' E := by
  apply Subtype.ext; ext a; simp

/-- The image of the zero derivation is zero. -/
theorem mapDeriv_zero (hI' : I' * I' = ⊥) : h.mapDeriv hI' (0 : Deriv I φ) = 0 := by
  apply Subtype.ext; ext a; simp

/-- `mapDeriv` as a `k`-linear map. -/
def mapDerivₗ (hI' : I' * I' = ⊥) : Deriv I φ →ₗ[k] Deriv I' φ' where
  toFun := h.mapDeriv hI'
  map_add' := h.mapDeriv_add hI'
  map_smul' := by intro c D; apply Subtype.ext; ext a; simp

/-- `mapDerivₗ` is `mapDeriv`. -/
@[simp] theorem mapDerivₗ_apply (hI' : I' * I' = ⊥) (D : Deriv I φ) :
    h.mapDerivₗ hI' D = h.mapDeriv hI' D := rfl

end SqZeroHom

end Functoriality

section Units

variable {P : Type*} [CommRing P] {I : Ideal P}

/-- The unit `1 + x` of `P`, for `x` in a square-zero ideal `I`. -/
def oneAddUnit (hI : I * I = ⊥) (x : I) : Pˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by linear_combination (-1 : P) * mul_eq_zero_of_mem_of_mul_eq_bot I hI x.2 x.2
  inv_val := by linear_combination (-1 : P) * mul_eq_zero_of_mem_of_mul_eq_bot I hI x.2 x.2

/-- The underlying element of `oneAddUnit hI x` is `1 + x`. -/
@[simp] theorem val_oneAddUnit (hI : I * I = ⊥) (x : I) : ((oneAddUnit hI x : Pˣ) : P) = 1 + x :=
  rfl

/-- `1 + (x + y) = (1 + x) (1 + y)` for `x`, `y` in a square-zero ideal. -/
theorem oneAddUnit_add (hI : I * I = ⊥) (x y : I) :
    oneAddUnit hI (x + y) = oneAddUnit hI x * oneAddUnit hI y := by
  ext
  simp only [val_oneAddUnit, Units.val_mul, Submodule.coe_add]
  linear_combination (-1 : P) * mul_eq_zero_of_mem_of_mul_eq_bot I hI x.2 y.2

/-- The ratio `u / v ∈ 1 + I` of two units of `P` with the same image modulo a square-zero
ideal `I`: the element `x ∈ I` with `u = (1 + x) v`. -/
def unitRatio (u v : Pˣ)
    (h : Ideal.Quotient.mk I (u : P) = Ideal.Quotient.mk I (v : P)) : I :=
  ⟨((u : P) - v) * ((v⁻¹ : Pˣ) : P), I.mul_mem_right _ (Ideal.Quotient.eq.1 h)⟩

/-- `u = (1 + x) v`, where `x` is the ratio `unitRatio u v`. -/
theorem unit_eq_oneAddUnit_mul (hI : I * I = ⊥) (u v : Pˣ)
    (h : Ideal.Quotient.mk I (u : P) = Ideal.Quotient.mk I (v : P)) :
    u = oneAddUnit hI (unitRatio u v h) * v := by
  ext
  simp only [Units.val_mul, val_oneAddUnit, unitRatio]
  linear_combination (-((u : P) - v)) * v.inv_mul

/-- If `(1 + x) v = (1 + y) v` then `x = y`. -/
theorem oneAddUnit_mul_right_cancel (hI : I * I = ⊥) {x y : I} {v : Pˣ}
    (h : oneAddUnit hI x * v = oneAddUnit hI y * v) : x = y :=
  Subtype.ext (by simpa using congrArg Units.val (mul_right_cancel h))

/-- If `u = (1 + x) v` then the ratio `unitRatio u v` is `x`. -/
theorem unitRatio_eq_of_eq (hI : I * I = ⊥) {u v : Pˣ}
    (h : Ideal.Quotient.mk I (u : P) = Ideal.Quotient.mk I (v : P)) {x : I}
    (hx : u = oneAddUnit hI x * v) : unitRatio u v h = x :=
  oneAddUnit_mul_right_cancel hI ((unit_eq_oneAddUnit_mul hI u v h).symm.trans hx)

/-- **The ratio of transition functions is a cocycle**: if `a b = c` and `a' b' = c'` with all
six units congruent modulo a square-zero ideal `I` (`a ≡ a'`, `b ≡ b'`, `c ≡ c'`) then the ratios
`1 + x`, `1 + y`, `1 + z` satisfy `x + y = z`. -/
theorem unitRatio_add_of_mul_eq (hI : I * I = ⊥) {a b c a' b' c' : Pˣ} (hc : a * b = c)
    (hc' : a' * b' = c')
    (ha : Ideal.Quotient.mk I (a' : P) = Ideal.Quotient.mk I (a : P))
    (hb : Ideal.Quotient.mk I (b' : P) = Ideal.Quotient.mk I (b : P))
    (hc2 : Ideal.Quotient.mk I (c' : P) = Ideal.Quotient.mk I (c : P)) :
    unitRatio a' a ha + unitRatio b' b hb = unitRatio c' c hc2 := by
  symm
  apply unitRatio_eq_of_eq
  have e1 := unit_eq_oneAddUnit_mul hI a' a ha
  have e2 := unit_eq_oneAddUnit_mul hI b' b hb
  rw [oneAddUnit_add, ← hc]
  calc c' = a' * b' := hc'.symm
    _ = (oneAddUnit hI (unitRatio a' a ha) * a) * (oneAddUnit hI (unitRatio b' b hb) * b) := by
      rw [← e1, ← e2]
    _ = _ := mul_mul_mul_comm _ _ _ _

end Units

/-! ### Čech cohomology of a presheaf of modules on a finite cover -/

section Cech

/-- A presheaf of `k`-modules on the nerve of a cover indexed by `ι`: the module `F s` of
sections over the intersection `U_s = ⋂_{i ∈ s} U_i`, with restriction maps `F s → F t` for
`s ⊆ t`. -/
structure CechPresheaf (k : Type*) [CommRing k] (ι : Type*) where
  /-- The sections over `U_s`. -/
  obj : Finset ι → Type v
  [addCommGroup : ∀ s, AddCommGroup (obj s)]
  [module : ∀ s, Module k (obj s)]
  /-- Restriction from `U_s` to `U_t` (`s ⊆ t`). -/
  res : ∀ {s t : Finset ι}, s ⊆ t → obj s →ₗ[k] obj t
  res_refl : ∀ {s : Finset ι} (h : s ⊆ s) (x : obj s), res h x = x
  res_comp : ∀ {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : obj s),
    res h₂ (res h₁ x) = res (h₁.trans h₂) x

namespace CechPresheaf

attribute [instance] addCommGroup module

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι] (F : CechPresheaf.{v} k ι)

/-- `{i} ⊆ {i, j}`. -/
theorem sub_pair_left (i j : ι) : ({i} : Finset ι) ⊆ {i, j} := by simp
/-- `{j} ⊆ {i, j}`. -/
theorem sub_pair_right (i j : ι) : ({j} : Finset ι) ⊆ {i, j} := by simp
/-- `{i, j} ⊆ {i, j, l}`. -/
theorem pair_sub_triple₁₂ (i j l : ι) : ({i, j} : Finset ι) ⊆ {i, j, l} := by
  simp [Finset.insert_subset_iff]
/-- `{j, l} ⊆ {i, j, l}`. -/
theorem pair_sub_triple₂₃ (i j l : ι) : ({j, l} : Finset ι) ⊆ {i, j, l} := by
  simp [Finset.insert_subset_iff]
/-- `{i, l} ⊆ {i, j, l}`. -/
theorem pair_sub_triple₁₃ (i j l : ι) : ({i, l} : Finset ι) ⊆ {i, j, l} := by
  simp [Finset.insert_subset_iff]

/-- Čech `1`-cochains: sections over the pairwise intersections `U_i ∩ U_j`. -/
abbrev C1 : Type _ := ∀ i j : ι, F.obj {i, j}

/-- Čech `0`-cochains: sections over the `U_i`. -/
abbrev C0 : Type _ := ∀ i : ι, F.obj {i}

/-- The Čech differential `C⁰ → C¹`: `(δc)_{ij} = c_j|_{U_ij} - c_i|_{U_ij}`. -/
def d0 : F.C0 →ₗ[k] F.C1 where
  toFun c i j := F.res (sub_pair_right i j) (c j) - F.res (sub_pair_left i j) (c i)
  map_add' := by intro c c'; ext i j; simp only [Pi.add_apply, map_add]; abel
  map_smul' := by intro r c; ext i j; simp [smul_sub]

/-- A Čech `1`-cocycle: `b_{jl} - b_{il} + b_{ij} = 0` on `U_i ∩ U_j ∩ U_l`. -/
def IsCocycle (b : F.C1) : Prop :=
  ∀ i j l : ι, F.res (pair_sub_triple₂₃ i j l) (b j l) - F.res (pair_sub_triple₁₃ i j l) (b i l)
    + F.res (pair_sub_triple₁₂ i j l) (b i j) = 0

/-- The submodule of Čech `1`-cocycles. -/
def Z1 : Submodule k F.C1 where
  carrier := {b | F.IsCocycle b}
  zero_mem' := by intro i j l; simp
  add_mem' := by
    intro b b' hb hb' i j l
    have := congrArg₂ (· + ·) (hb i j l) (hb' i j l)
    simp only [Pi.add_apply, map_add, add_zero] at this ⊢
    rw [← this]; abel
  smul_mem' := by
    intro r b hb i j l
    have := congrArg (r • ·) (hb i j l)
    simp only [Pi.smul_apply, map_smul, smul_add, smul_sub, smul_zero] at this ⊢
    exact this

/-- A Čech coboundary is a cocycle. -/
theorem isCocycle_d0 (c : F.C0) : F.IsCocycle (F.d0 c) := by
  intro i j l
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk, map_sub, F.res_comp]
  abel

/-- The Čech coboundaries, as a submodule of the cocycles. -/
def B1 : Submodule k F.Z1 := (LinearMap.range F.d0).comap F.Z1.subtype

/-- The first Čech cohomology `Ȟ¹(𝔘, F)` of the presheaf on the cover: cocycles modulo
coboundaries. -/
abbrev H1 : Type _ := F.Z1 ⧸ F.B1

/-- The class of a Čech `1`-cocycle. -/
def cls (b : F.C1) (hb : F.IsCocycle b) : F.H1 := Submodule.Quotient.mk ⟨b, hb⟩

/-- The class of a cocycle vanishes iff the cocycle is a coboundary. -/
theorem cls_eq_zero_iff {b : F.C1} (hb : F.IsCocycle b) : F.cls b hb = 0 ↔ ∃ c, F.d0 c = b := by
  unfold cls
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-- Two cocycles have the same class iff their difference is a coboundary. -/
theorem cls_eq_cls_iff {b b' : F.C1} (hb : F.IsCocycle b) (hb' : F.IsCocycle b') :
    F.cls b hb = F.cls b' hb' ↔ ∃ c, F.d0 c = b - b' := by
  have hbb : F.IsCocycle (b - b') :=
    (F.Z1).sub_mem (show b ∈ F.Z1 from hb) (show b' ∈ F.Z1 from hb')
  have : F.cls b hb - F.cls b' hb' = F.cls (b - b') hbb := rfl
  rw [← sub_eq_zero, this, cls_eq_zero_iff]

end CechPresheaf

/-- A presheaf of pseudo-torsors under a presheaf of modules `F` on the nerve of a cover: sets
`X s` with restriction maps, on which `F s` acts simply transitively, compatibly with restriction.
In the application `X s` is the set of lifts over `U_s` of a map to a square-zero thickening, and
`F s` the module of derivations `f^*T_U ⊗ J` over `U_s`. -/
structure CechTorsor {k : Type*} [CommRing k] {ι : Type*} (F : CechPresheaf.{v} k ι) where
  /-- The sets of local objects over `U_s`. -/
  X : Finset ι → Type v
  res : ∀ {s t : Finset ι}, s ⊆ t → X s → X t
  res_refl : ∀ {s : Finset ι} (h : s ⊆ s) (x : X s), res h x = x
  res_comp : ∀ {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : X s),
    res h₂ (res h₁ x) = res (h₁.trans h₂) x
  /-- The action of `F s` on `X s`. -/
  vadd : ∀ s, F.obj s → X s → X s
  /-- The difference of two local objects. -/
  vsub : ∀ s, X s → X s → F.obj s
  vadd_zero : ∀ s (x : X s), vadd s 0 x = x
  vadd_add : ∀ s (g h : F.obj s) (x : X s), vadd s (g + h) x = vadd s g (vadd s h x)
  vsub_vadd : ∀ s (x y : X s), vadd s (vsub s x y) y = x
  vadd_vsub : ∀ s (g : F.obj s) (y : X s), vsub s (vadd s g y) y = g
  res_vadd : ∀ {s t : Finset ι} (h : s ⊆ t) (g : F.obj s) (x : X s),
    res h (vadd s g x) = vadd t (F.res h g) (res h x)

namespace CechTorsor

attribute [local instance] CechPresheaf.addCommGroup CechPresheaf.module

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι] {F : CechPresheaf.{v} k ι}
  (T : CechTorsor F)

/-- Restriction commutes with taking differences of local objects. -/
theorem vsub_res {s t : Finset ι} (h : s ⊆ t) (x y : T.X s) :
    F.res h (T.vsub s x y) = T.vsub t (T.res h x) (T.res h y) := by
  conv_rhs => rw [← T.vsub_vadd s x y, T.res_vadd, T.vadd_vsub]

/-- `(x - y) + (y - z) = x - z` for local objects `x`, `y`, `z`. -/
theorem vsub_add_vsub (s : Finset ι) (x y z : T.X s) :
    T.vsub s x y + T.vsub s y z = T.vsub s x z := by
  have e : T.vadd s (T.vsub s x y + T.vsub s y z) z = x := by
    rw [T.vadd_add, T.vsub_vadd, T.vsub_vadd]
  conv_rhs => rw [← e, T.vadd_vsub]

/-- The difference of a local object with itself is zero. -/
theorem vsub_self (s : Finset ι) (x : T.X s) : T.vsub s x x = 0 := by
  have := T.vadd_vsub s 0 x
  rwa [T.vadd_zero] at this

/-- Local objects with zero difference are equal. -/
theorem eq_of_vsub_eq_zero (s : Finset ι) {x y : T.X s} (h : T.vsub s x y = 0) : x = y := by
  rw [← T.vsub_vadd s x y, h, T.vadd_zero]

/-- `(g + p) - (h + q) = g - h + (p - q)`. -/
theorem vsub_vadd_vadd (s : Finset ι) (g h : F.obj s) (p q : T.X s) :
    T.vsub s (T.vadd s g p) (T.vadd s h q) = g - h + T.vsub s p q := by
  have e1 : T.vadd s g p = T.vadd s (g - h + T.vsub s p q) (T.vadd s h q) := by
    rw [← T.vadd_add, show g - h + T.vsub s p q + h = g + T.vsub s p q by abel, T.vadd_add,
      T.vsub_vadd]
  rw [e1, T.vadd_vsub]

/-- The Čech `1`-cochain of differences of a family of local objects `x_i ∈ X(U_i)`:
`b_{ij} = x_j|_{U_ij} - x_i|_{U_ij}`. -/
def cechDiff (x : ∀ i : ι, T.X {i}) : F.C1 := fun i j =>
  T.vsub _ (T.res (CechPresheaf.sub_pair_right i j) (x j))
    (T.res (CechPresheaf.sub_pair_left i j) (x i))

/-- The cochain of differences of a family of local objects is a Čech cocycle. -/
theorem isCocycle_cechDiff (x : ∀ i : ι, T.X {i}) : F.IsCocycle (T.cechDiff x) := by
  intro i j l
  simp only [cechDiff, T.vsub_res, T.res_comp]
  have aux : ∀ a b c : T.X {i, j, l},
      T.vsub _ c b - T.vsub _ c a + T.vsub _ b a = 0 := by
    intro a b c
    rw [← T.vsub_add_vsub _ c b a]; abel
  exact aux _ _ _

/-- The first obstruction: the Čech class of the differences of any family of local objects. -/
def obstruction (x : ∀ i : ι, T.X {i}) : F.H1 := F.cls (T.cechDiff x) (T.isCocycle_cechDiff x)

/-- Translating the local objects by a `0`-cochain `c` adds `δc` to their cochain of
differences. -/
theorem cechDiff_vadd (c : F.C0) (x : ∀ i : ι, T.X {i}) :
    T.cechDiff (fun i => T.vadd _ (c i) (x i)) = T.cechDiff x + F.d0 c := by
  ext i j
  simp only [cechDiff, T.res_vadd, T.vsub_vadd_vadd, Pi.add_apply, CechPresheaf.d0,
    LinearMap.coe_mk, AddHom.coe_mk]
  abel

/-- The obstruction class does not depend on the family of local objects chosen. -/
theorem obstruction_eq (x y : ∀ i : ι, T.X {i}) : T.obstruction x = T.obstruction y := by
  rw [obstruction, obstruction, CechPresheaf.cls_eq_cls_iff]
  refine ⟨fun i => T.vsub _ (x i) (y i), ?_⟩
  have := T.cechDiff_vadd (fun i => T.vsub _ (x i) (y i)) y
  simp only [T.vsub_vadd] at this
  rw [this]; abel

/-- **Čech gluing criterion**: the obstruction class vanishes iff the local objects can be
modified (by zero-cochains) so as to agree on the overlaps, i.e. glue. -/
theorem obstruction_eq_zero_iff (x : ∀ i : ι, T.X {i}) :
    T.obstruction x = 0 ↔ ∃ y : ∀ i : ι, T.X {i}, ∀ i j : ι,
      T.res (CechPresheaf.sub_pair_left i j) (y i) =
        T.res (CechPresheaf.sub_pair_right i j) (y j) := by
  rw [obstruction, CechPresheaf.cls_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i => T.vadd _ (-c i) (x i), fun i j => ?_⟩
    have := congrFun (congrFun (T.cechDiff_vadd (-c) x) i) j
    rw [map_neg F.d0 c, hc] at this
    simp only [Pi.add_apply, Pi.neg_apply, add_neg_cancel] at this
    exact (T.eq_of_vsub_eq_zero _ this).symm
  · rintro ⟨y, hy⟩
    refine ⟨fun i => T.vsub _ (x i) (y i), ?_⟩
    have := T.cechDiff_vadd (fun i => T.vsub _ (x i) (y i)) y
    simp only [T.vsub_vadd] at this
    have h0 : T.cechDiff y = 0 := by
      ext i j
      simp only [cechDiff, hy i j, T.vsub_self]; rfl
    rw [this, h0, zero_add]

end CechTorsor

/-- A morphism of presheaves of `k`-modules on the nerve of the cover. -/
structure CechPresheaf.Hom {k : Type*} [CommRing k] {ι : Type*} (F G : CechPresheaf.{v} k ι) where
  /-- The component at `s`. -/
  map : ∀ s : Finset ι, F.obj s →ₗ[k] G.obj s
  map_res : ∀ {s t : Finset ι} (h : s ⊆ t) (x : F.obj s), map t (F.res h x) = G.res h (map s x)

namespace CechPresheaf.Hom

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι] {F G : CechPresheaf.{v} k ι}
  (φ : Hom F G)

/-- The map on Čech `1`-cochains. -/
def c1 : F.C1 →ₗ[k] G.C1 where
  toFun b i j := φ.map _ (b i j)
  map_add' := by intro b b'; ext i j; simp
  map_smul' := by intro r b; ext i j; simp

/-- The map on `1`-cochains commutes with the Čech differential. -/
theorem c1_d0 (c : F.C0) : φ.c1 (F.d0 c) = G.d0 (fun i => φ.map _ (c i)) := by
  ext i j
  simp [c1, CechPresheaf.d0, φ.map_res]

/-- The image of a Čech cocycle is a cocycle. -/
theorem isCocycle_c1 {b : F.C1} (hb : F.IsCocycle b) : G.IsCocycle (φ.c1 b) := by
  intro i j l
  have := congrArg (φ.map {i, j, l}) (hb i j l)
  simpa [c1, φ.map_res] using this

/-- The induced map on first Čech cohomology. -/
def h1 : F.H1 →ₗ[k] G.H1 :=
  Submodule.mapQ F.B1 G.B1
    ((φ.c1.restrict (fun b hb => φ.isCocycle_c1 hb) : F.Z1 →ₗ[k] G.Z1))
    (by
      rintro ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨fun i => φ.map _ (c i), ?_⟩
      change G.d0 _ = φ.c1 b
      rw [← φ.c1_d0, hc]; rfl)

/-- The induced map on `Ȟ¹` sends the class of a cocycle to the class of its image. -/
theorem h1_cls {b : F.C1} (hb : F.IsCocycle b) :
    φ.h1 (F.cls b hb) = G.cls (φ.c1 b) (φ.isCocycle_c1 hb) := rfl

end CechPresheaf.Hom

/-- A morphism of pseudo-torsors over a morphism `φ` of presheaves of modules. -/
structure CechTorsor.Hom {k : Type*} [CommRing k] {ι : Type*} {F G : CechPresheaf.{v} k ι}
    (T : CechTorsor F) (T' : CechTorsor G) (φ : CechPresheaf.Hom F G) where
  /-- The component at `s`. -/
  map : ∀ s : Finset ι, T.X s → T'.X s
  map_res : ∀ {s t : Finset ι} (h : s ⊆ t) (x : T.X s), map t (T.res h x) = T'.res h (map s x)
  map_vadd : ∀ (s : Finset ι) (g : F.obj s) (x : T.X s),
    map s (T.vadd s g x) = T'.vadd s (φ.map s g) (map s x)

namespace CechTorsor.Hom

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι] {F G : CechPresheaf.{v} k ι}
  {T : CechTorsor F} {T' : CechTorsor G} {φ : CechPresheaf.Hom F G} (m : T.Hom T' φ)

/-- A morphism of torsors carries differences of local objects to differences of their
images. -/
theorem map_vsub (s : Finset ι) (x y : T.X s) :
    φ.map s (T.vsub s x y) = T'.vsub s (m.map s x) (m.map s y) := by
  conv_rhs => rw [← T.vsub_vadd s x y, m.map_vadd, T'.vadd_vsub]

/-- **Naturality of the first obstruction**: a morphism of torsors carries the obstruction class
of a family of local objects to that of the image family. -/
theorem obstruction_map (x : ∀ i : ι, T.X {i}) :
    φ.h1 (T.obstruction x) = T'.obstruction (fun i => m.map _ (x i)) := by
  rw [CechTorsor.obstruction, CechPresheaf.Hom.h1_cls, CechTorsor.obstruction]
  congr 1
  ext i j
  simp [CechPresheaf.Hom.c1, CechTorsor.cechDiff, m.map_vsub, m.map_res]

end CechTorsor.Hom

end Cech

/-! ### The Čech torsor of local lifts over a cover -/

section LiftCover

/-- The data of a lifting problem for a map from the `k`-algebra `S` (a smooth affine chart of the
target) to the thickened curve, over a cover indexed by `ι`: for each intersection `U_s` of members
of the cover, a `k`-algebra `P s` (sections of `𝒪` of `C_{A'}` over `U_s`), a square-zero ideal
`I s` (the kernel of restriction to `C_A`, resp. `J ⊗ 𝔟` for the maps fixed on the marked
points), and the given map `φ s : S → P s / I s`, all compatible with restriction. -/
structure LiftCover (k : Type*) [CommRing k] (S : Type v) [CommRing S] [Algebra k S]
    (ι : Type*) where
  /-- The rings of sections over `U_s`. -/
  P : Finset ι → Type v
  [commRing : ∀ s, CommRing (P s)]
  [algebra : ∀ s, Algebra k (P s)]
  /-- The square-zero ideals. -/
  I : ∀ s, Ideal (P s)
  hI : ∀ s, I s * I s = ⊥
  /-- The given maps. -/
  φ : ∀ s, S →ₐ[k] P s ⧸ I s
  /-- Restriction. -/
  hom : ∀ {s t : Finset ι}, s ⊆ t → SqZeroHom (I s) (φ s) (I t) (φ t)
  hom_refl : ∀ {s : Finset ι} (h : s ⊆ s) (x : P s), (hom h).ψ x = x
  hom_comp : ∀ {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : P s),
    (hom h₂).ψ ((hom h₁).ψ x) = (hom (h₁.trans h₂)).ψ x

namespace LiftCover

attribute [instance] commRing algebra

variable {k : Type*} [CommRing k] {S : Type v} [CommRing S] [Algebra k S] {ι : Type*}
  [DecidableEq ι] (C : LiftCover.{v} k S ι)

/-- The presheaf of derivations `S → I_s` along `φ_s`: `Γ(U_s, f^*T_U ⊗ J)`. -/
def derivPresheaf : CechPresheaf.{v} k ι where
  obj s := Deriv (C.I s) (C.φ s)
  res h := (C.hom h).mapDerivₗ (C.hI _)
  res_refl h x := by
    apply Subtype.ext; ext a
    exact C.hom_refl h _
  res_comp h₁ h₂ x := by
    apply Subtype.ext; ext a
    exact C.hom_comp h₁ h₂ _

/-- The pseudo-torsor of local lifts of `φ_s` to `P s`, under the derivations. -/
def liftTorsor : CechTorsor C.derivPresheaf where
  X s := LiftsOf (C.I s) (C.φ s)
  res h := (C.hom h).mapLift
  res_refl h x := by
    apply Subtype.ext; ext a
    exact C.hom_refl h _
  res_comp h₁ h₂ x := by
    apply Subtype.ext; ext a
    exact C.hom_comp h₁ h₂ _
  vadd s D g := g.add (C.hI s) D
  vsub s g₁ g₂ := g₁.sub (C.hI s) g₂
  vadd_zero s x := x.add_zero (C.hI s)
  vadd_add s D E x :=
    (congrArg (LiftsOf.add (C.hI s) x) (add_comm D E)).trans (LiftsOf.add_add (C.hI s) x E D).symm
  vsub_vadd s x y := LiftsOf.sub_add_cancel (C.hI s) x y
  vadd_vsub s D y := LiftsOf.add_sub_cancel (C.hI s) y D
  res_vadd h D x := (C.hom h).mapLift_add (C.hI _) (C.hI _) x D

/-- **First obstruction** (affine-chart form, independent of the choice of local lifts): the Čech
class in `Ȟ¹(𝔘, 𝒟)`, `𝒟 = derivations along φ`, of the differences of local lifts. -/
def firstObstruction (x : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i})) : C.derivPresheaf.H1 :=
  C.liftTorsor.obstruction x

/-- The first obstruction does not depend on the family of local lifts chosen. -/
theorem firstObstruction_eq (x y : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i})) :
    C.firstObstruction x = C.firstObstruction y :=
  C.liftTorsor.obstruction_eq x y

/-- The first obstruction vanishes iff the local lifts can be modified, by derivations on the
`U_i`, to a compatible family of local lifts. -/
theorem firstObstruction_eq_zero_iff (x : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i})) :
    C.firstObstruction x = 0 ↔ ∃ y : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i}), ∀ i j : ι,
      (C.hom (CechPresheaf.sub_pair_left i j)).mapLift (y i) =
        (C.hom (CechPresheaf.sub_pair_right i j)).mapLift (y j) :=
  C.liftTorsor.obstruction_eq_zero_iff x

/-- Smooth lifting: the local lifts exist over each `U_i` when `S` is formally smooth. -/
theorem nonempty_liftsOf [Algebra.FormallySmooth k S] (s : Finset ι) :
    Nonempty (LiftsOf (C.I s) (C.φ s)) :=
  LiftsOf.nonempty (C.hI s) (C.φ s)

/-- A morphism of lifting problems over a cover (in the application, the quotient of the
extension by a subspace of `J`). -/
structure Hom (C C' : LiftCover.{v} k S ι) where
  /-- The component maps. -/
  sq : ∀ s, SqZeroHom (C.I s) (C.φ s) (C'.I s) (C'.φ s)
  comm : ∀ {s t : Finset ι} (h : s ⊆ t) (x : C.P s),
    (sq t).ψ ((C.hom h).ψ x) = (C'.hom h).ψ ((sq s).ψ x)

variable {C} {C' : LiftCover.{v} k S ι} (m : C.Hom C')

/-- The induced morphism of presheaves of derivations. -/
def Hom.derivHom : C.derivPresheaf.Hom C'.derivPresheaf where
  map s := (m.sq s).mapDerivₗ (C'.hI s)
  map_res h x := by
    apply Subtype.ext; ext a
    exact m.comm h _

/-- The induced morphism of torsors of local lifts. -/
def Hom.liftHom : C.liftTorsor.Hom C'.liftTorsor m.derivHom where
  map s := (m.sq s).mapLift
  map_res h x := by
    apply Subtype.ext; ext a
    exact m.comm h _
  map_vadd s D x := (m.sq s).mapLift_add (C.hI s) (C'.hI s) x D

/-- **Naturality of the first obstruction** under a morphism of lifting problems. -/
theorem Hom.firstObstruction_map (x : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i})) :
    m.derivHom.h1 (C.firstObstruction x) =
      C'.firstObstruction (fun i => (m.sq _).mapLift (x i)) :=
  m.liftHom.obstruction_map x

/-- The presheaf of square-zero ideals `I_s ⊆ P_s` (`J ⊗ 𝒪_C` over `U_s`), in which the
transition functions `1 + u_ij` of the comparison of two line bundles take their values. -/
def idealPresheaf : CechPresheaf.{v} k ι where
  obj s := (C.I s).restrictScalars k
  res h := ((C.hom h).ψ.toLinearMap).restrict (fun x hx => (C.hom h).mem x hx)
  res_refl h x := Subtype.ext (C.hom_refl h _)
  res_comp h₁ h₂ x := Subtype.ext (C.hom_comp h₁ h₂ _)

/-- Restriction of units. -/
def resUnit {s t : Finset ι} (h : s ⊆ t) : (C.P s)ˣ →* (C.P t)ˣ :=
  Units.map (C.hom h).ψ.toMonoidHom

/-- The value of a restricted unit is the restriction of its value. -/
@[simp] theorem coe_resUnit {s t : Finset ι} (h : s ⊆ t) (u : (C.P s)ˣ) :
    ((C.resUnit h u : (C.P t)ˣ) : C.P t) = (C.hom h).ψ (u : C.P s) := rfl

/-- Restriction preserves congruence of units modulo the ideals. -/
theorem mk_resUnit_eq {s t : Finset ι} (h : s ⊆ t) {u v : (C.P s)ˣ}
    (huv : Ideal.Quotient.mk (C.I s) (u : C.P s) = Ideal.Quotient.mk (C.I s) (v : C.P s)) :
    Ideal.Quotient.mk (C.I t) ((C.resUnit h u : (C.P t)ˣ) : C.P t) =
      Ideal.Quotient.mk (C.I t) ((C.resUnit h v : (C.P t)ˣ) : C.P t) := by
  have := (C.hom h).mem _ (Ideal.Quotient.eq.1 huv)
  rw [Ideal.Quotient.eq]
  simpa [resUnit] using this

/-- The ratio of the restrictions of two units is the restriction of their ratio. -/
theorem unitRatio_resUnit {s t : Finset ι} (h : s ⊆ t) {u v : (C.P s)ˣ}
    (huv : Ideal.Quotient.mk (C.I s) (u : C.P s) = Ideal.Quotient.mk (C.I s) (v : C.P s)) :
    ((unitRatio (C.resUnit h u) (C.resUnit h v) (C.mk_resUnit_eq h huv) : C.I t) : C.P t) =
      (C.hom h).ψ ((unitRatio u v huv : C.I s) : C.P s) := by
  simp [unitRatio, resUnit, map_mul, map_sub]

/-- A system of transition functions on the cover: units `g_ij ∈ P_{ij}^×` satisfying the cocycle
condition `g_ij g_jl = g_il` on `U_ijl`. -/
def IsUnitCocycle (g : ∀ i j : ι, (C.P {i, j})ˣ) : Prop :=
  ∀ i j l : ι, C.resUnit (CechPresheaf.pair_sub_triple₁₂ i j l) (g i j) *
    C.resUnit (CechPresheaf.pair_sub_triple₂₃ i j l) (g j l) =
    C.resUnit (CechPresheaf.pair_sub_triple₁₃ i j l) (g i l)

/-- The ratio cochain `u_ij`, `g'_ij = (1 + u_ij) g_ij`, of two systems of transition functions
that agree modulo the ideals. -/
def ratioCochain (g g' : ∀ i j : ι, (C.P {i, j})ˣ)
    (hc : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j})) : C.idealPresheaf.C1 :=
  fun i j => unitRatio (g' i j) (g i j) (hc i j)

/-- The ratio cochain of two systems of transition functions is a Čech cocycle of the ideal
presheaf. -/
theorem isCocycle_ratioCochain {g g' : ∀ i j : ι, (C.P {i, j})ˣ} (hg : C.IsUnitCocycle g)
    (hg' : C.IsUnitCocycle g')
    (hc : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j})) :
    C.idealPresheaf.IsCocycle (C.ratioCochain g g' hc) := by
  intro i j l
  apply Subtype.ext
  have key := unitRatio_add_of_mul_eq (C.hI {i, j, l}) (hg i j l) (hg' i j l)
    (C.mk_resUnit_eq _ (hc i j)) (C.mk_resUnit_eq _ (hc j l)) (C.mk_resUnit_eq _ (hc i l))
  have key' := congrArg (fun x : C.I {i, j, l} => (x : C.P {i, j, l})) key
  simp only [Submodule.coe_add] at key'
  rw [C.unitRatio_resUnit _ (hc i j), C.unitRatio_resUnit _ (hc j l),
    C.unitRatio_resUnit _ (hc i l)] at key'
  have goal : (C.hom (CechPresheaf.pair_sub_triple₂₃ i j l)).ψ
      (C.ratioCochain g g' hc j l).1 -
      (C.hom (CechPresheaf.pair_sub_triple₁₃ i j l)).ψ
        (C.ratioCochain g g' hc i l).1 +
      (C.hom (CechPresheaf.pair_sub_triple₁₂ i j l)).ψ
        (C.ratioCochain g g' hc i j).1 = 0 := by
    simp only [ratioCochain]
    linear_combination key'
  exact goal

/-- **Second obstruction**: the Čech class of the ratio of two systems of transition functions
that agree modulo the ideals. -/
def secondObstruction {g g' : ∀ i j : ι, (C.P {i, j})ˣ} (hg : C.IsUnitCocycle g)
    (hg' : C.IsUnitCocycle g')
    (hc : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j})) : C.idealPresheaf.H1 :=
  C.idealPresheaf.cls (C.ratioCochain g g' hc) (C.isCocycle_ratioCochain hg hg' hc)

/-- If the second obstruction vanishes, the systems of transition functions are isomorphic, by an
isomorphism `e_i ∈ P_i^×` that is the identity modulo the ideals. -/
theorem exists_iso_of_secondObstruction_eq_zero {g g' : ∀ i j : ι, (C.P {i, j})ˣ}
    (hg : C.IsUnitCocycle g) (hg' : C.IsUnitCocycle g')
    (hc : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j}))
    (h0 : C.secondObstruction hg hg' hc = 0) :
    ∃ e : ∀ i : ι, (C.P {i})ˣ, (∀ i, Ideal.Quotient.mk (C.I {i}) (e i : C.P {i}) = 1) ∧
      ∀ i j : ι, g' i j * C.resUnit (CechPresheaf.sub_pair_left i j) (e i) =
        C.resUnit (CechPresheaf.sub_pair_right i j) (e j) * g i j := by
  obtain ⟨c, hc0⟩ := (C.idealPresheaf.cls_eq_zero_iff _).1 h0
  let c' : ∀ i : ι, C.I {i} := fun i => ⟨(c i).1, (c i).2⟩
  refine ⟨fun i => oneAddUnit (C.hI {i}) (c' i), fun i => ?_, fun i j => ?_⟩
  · simp [Ideal.Quotient.eq_zero_iff_mem.2 (c' i).2]
  · have hu := congrArg Subtype.val (congrFun (congrFun hc0 i) j)
    have A := congrArg Units.val (unit_eq_oneAddUnit_mul (C.hI {i, j}) (g' i j) (g i j) (hc i j))
    have z1 := mul_eq_zero_of_mem_of_mul_eq_bot (C.I {i, j}) (C.hI {i, j})
      ((C.hom (CechPresheaf.sub_pair_left i j)).mem _ (c' i).2)
      ((C.hom (CechPresheaf.sub_pair_left i j)).mem _ (c' i).2)
    have z2 := mul_eq_zero_of_mem_of_mul_eq_bot (C.I {i, j}) (C.hI {i, j})
      ((C.hom (CechPresheaf.sub_pair_right i j)).mem _ (c' j).2)
      ((C.hom (CechPresheaf.sub_pair_left i j)).mem _ (c' i).2)
    apply Units.ext
    simp only [CechPresheaf.d0, LinearMap.coe_mk, AddHom.coe_mk] at hu
    have hu' : (C.hom (CechPresheaf.sub_pair_right i j)).ψ (c' j : C.P {j}) -
        (C.hom (CechPresheaf.sub_pair_left i j)).ψ (c' i : C.P {i}) =
        ((unitRatio (g' i j) (g i j) (hc i j) : C.I {i, j}) : C.P {i, j}) := hu
    simp only [Units.val_mul, val_oneAddUnit] at A
    rw [← hu'] at A
    have hres : ∀ (s t : Finset ι) (h : s ⊆ t) (x : C.I s),
        ((C.resUnit h (oneAddUnit (C.hI s) x) : (C.P t)ˣ) : C.P t) =
          1 + (C.hom h).ψ (x : C.P s) := by
      intro s t h x
      simp [resUnit]
    simp only [Units.val_mul, hres] at A ⊢
    linear_combination (1 + (C.hom (CechPresheaf.sub_pair_left i j)).ψ (c' i : C.P {i})) * A
      + (g i j : C.P {i, j}) * z2 - (g i j : C.P {i, j}) * z1

/-- Conversely, an isomorphism of the systems of transition functions that is the identity modulo
the ideals kills the second obstruction. -/
theorem secondObstruction_eq_zero_of_iso {g g' : ∀ i j : ι, (C.P {i, j})ˣ}
    (hg : C.IsUnitCocycle g) (hg' : C.IsUnitCocycle g')
    (hc : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j}))
    (e : ∀ i : ι, (C.P {i})ˣ) (he : ∀ i, Ideal.Quotient.mk (C.I {i}) (e i : C.P {i}) = 1)
    (hiso : ∀ i j : ι, g' i j * C.resUnit (CechPresheaf.sub_pair_left i j) (e i) =
        C.resUnit (CechPresheaf.sub_pair_right i j) (e j) * g i j) :
    C.secondObstruction hg hg' hc = 0 := by
  refine (C.idealPresheaf.cls_eq_zero_iff _).2 ?_
  have he' : ∀ i, Ideal.Quotient.mk (C.I {i}) (e i : C.P {i}) =
      Ideal.Quotient.mk (C.I {i}) (((1 : (C.P {i})ˣ) : C.P {i}) : C.P {i}) := fun i => by
    simpa using he i
  let c : ∀ i : ι, C.I {i} := fun i => unitRatio (e i) 1 (he' i)
  have hec : ∀ i, ((e i : (C.P {i})ˣ) : C.P {i}) = 1 + (c i : C.P {i}) := fun i => by
    simpa using congrArg Units.val (unit_eq_oneAddUnit_mul (C.hI {i}) (e i) 1 (he' i))
  refine ⟨fun i => ⟨(c i).1, (c i).2⟩, ?_⟩
  ext i j
  apply Subtype.ext
  have z1 := mul_eq_zero_of_mem_of_mul_eq_bot (C.I {i, j}) (C.hI {i, j})
    ((C.hom (CechPresheaf.sub_pair_left i j)).mem _ (c i).2)
    ((C.hom (CechPresheaf.sub_pair_left i j)).mem _ (c i).2)
  have z2 := mul_eq_zero_of_mem_of_mul_eq_bot (C.I {i, j}) (C.hI {i, j})
    ((C.hom (CechPresheaf.sub_pair_right i j)).mem _ (c j).2)
    ((C.hom (CechPresheaf.sub_pair_left i j)).mem _ (c i).2)
  have H := congrArg Units.val (hiso i j)
  rw [Units.val_mul, Units.val_mul, coe_resUnit, coe_resUnit, hec, hec, map_add, map_add] at H
  simp only [map_one] at H
  have hx : (C.hom (CechPresheaf.sub_pair_right i j)).ψ (c j : C.P {j}) -
      (C.hom (CechPresheaf.sub_pair_left i j)).ψ (c i : C.P {i}) ∈ C.I {i, j} :=
    (C.I {i, j}).sub_mem ((C.hom _).mem _ (c j).2) ((C.hom _).mem _ (c i).2)
  have hgg : g' i j = oneAddUnit (C.hI _) ⟨_, hx⟩ * g i j := by
    apply Units.ext
    simp only [Units.val_mul, val_oneAddUnit]
    linear_combination (1 - (C.hom (CechPresheaf.sub_pair_left i j)).ψ (c i : C.P {i})) * H
      + (g' i j : C.P {i, j}) * z1 - (g i j : C.P {i, j}) * z2
  exact congrArg Subtype.val (unitRatio_eq_of_eq (C.hI _) (hc i j) hgg).symm

/-- The second obstruction vanishes iff the systems of transition functions are isomorphic, by an
isomorphism `e_i ∈ P_i^×` that is the identity modulo the ideals. -/
theorem secondObstruction_eq_zero_iff {g g' : ∀ i j : ι, (C.P {i, j})ˣ}
    (hg : C.IsUnitCocycle g) (hg' : C.IsUnitCocycle g')
    (hc : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j})) :
    C.secondObstruction hg hg' hc = 0 ↔
      ∃ e : ∀ i : ι, (C.P {i})ˣ, (∀ i, Ideal.Quotient.mk (C.I {i}) (e i : C.P {i}) = 1) ∧
        ∀ i j : ι, g' i j * C.resUnit (CechPresheaf.sub_pair_left i j) (e i) =
          C.resUnit (CechPresheaf.sub_pair_right i j) (e j) * g i j :=
  ⟨C.exists_iso_of_secondObstruction_eq_zero hg hg' hc,
    fun ⟨e, he, hiso⟩ => C.secondObstruction_eq_zero_of_iso hg hg' hc e he hiso⟩

/-- The induced morphism of presheaves of ideals. -/
def Hom.idealHom : C.idealPresheaf.Hom C'.idealPresheaf where
  map s := ((m.sq s).ψ.toLinearMap).restrict (fun x hx => (m.sq s).mem x hx)
  map_res h x := Subtype.ext (m.comm h _)

/-- Image of a unit under a morphism of lifting problems. -/
def Hom.mapUnit (s : Finset ι) : (C.P s)ˣ →* (C'.P s)ˣ := Units.map (m.sq s).ψ.toMonoidHom

/-- The image of units under a morphism commutes with restriction. -/
theorem Hom.resUnit_mapUnit {s t : Finset ι} (h : s ⊆ t) (u : (C.P s)ˣ) :
    C'.resUnit h (m.mapUnit s u) = m.mapUnit t (C.resUnit h u) := by
  apply Units.ext
  simp [Hom.mapUnit, resUnit, m.comm h]

/-- The image of a system of transition functions is a system of transition functions. -/
theorem Hom.isUnitCocycle_map {g : ∀ i j : ι, (C.P {i, j})ˣ} (hg : C.IsUnitCocycle g) :
    C'.IsUnitCocycle (fun i j => m.mapUnit _ (g i j)) := by
  intro i j l
  simp only [m.resUnit_mapUnit, ← map_mul, hg i j l]

/-- A morphism preserves congruence of units modulo the ideals. -/
theorem Hom.mk_mapUnit {s : Finset ι} {u v : (C.P s)ˣ}
    (huv : Ideal.Quotient.mk (C.I s) (u : C.P s) = Ideal.Quotient.mk (C.I s) (v : C.P s)) :
    Ideal.Quotient.mk (C'.I s) ((m.mapUnit s u : (C'.P s)ˣ) : C'.P s) =
      Ideal.Quotient.mk (C'.I s) ((m.mapUnit s v : (C'.P s)ˣ) : C'.P s) := by
  have := (m.sq s).mem _ (Ideal.Quotient.eq.1 huv)
  rw [Ideal.Quotient.eq]
  simpa [Hom.mapUnit] using this

/-- The ratio of the images of two units is the image of their ratio. -/
theorem Hom.unitRatio_mapUnit {s : Finset ι} {u v : (C.P s)ˣ}
    (huv : Ideal.Quotient.mk (C.I s) (u : C.P s) = Ideal.Quotient.mk (C.I s) (v : C.P s)) :
    ((unitRatio (m.mapUnit s u) (m.mapUnit s v) (m.mk_mapUnit huv) : C'.I s) : C'.P s) =
      (m.sq s).ψ ((unitRatio u v huv : C.I s) : C.P s) := by
  simp [unitRatio, Hom.mapUnit, map_mul, map_sub]

/-- **Naturality of the second obstruction** under a morphism of lifting problems. -/
theorem Hom.secondObstruction_map {g g' : ∀ i j : ι, (C.P {i, j})ˣ} (hg : C.IsUnitCocycle g)
    (hg' : C.IsUnitCocycle g')
    (hc : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g i j : C.P {i, j})) :
    m.idealHom.h1 (C.secondObstruction hg hg' hc) =
      C'.secondObstruction (m.isUnitCocycle_map hg) (m.isUnitCocycle_map hg')
        (fun i j => m.mk_mapUnit (hc i j)) := by
  unfold secondObstruction
  rw [CechPresheaf.Hom.h1_cls]
  congr 1
  ext i j
  exact Subtype.ext (m.unitRatio_mapUnit (hc i j)).symm

end LiftCover

end LiftCover

/-! ### First-order deformations -/

section FirstOrder

open TrivSqZeroExt

variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [Algebra k S] [Algebra k R]

/-- A derivation of `S` along `φ : S → R` with values in `R`: a `k`-linear map `D` with
`D (a b) = φ a · D b + φ b · D a`. -/
def IsDerivAlong (φ : S →ₐ[k] R) (D : S →ₗ[k] R) : Prop :=
  ∀ a b : S, D (a * b) = φ a * D b + φ b * D a

/-- A derivation along `φ` kills `1`. -/
theorem IsDerivAlong.map_one {φ : S →ₐ[k] R} {D : S →ₗ[k] R} (hD : IsDerivAlong φ D) :
    D 1 = 0 := by
  have := hD 1 1
  simp only [mul_one, _root_.map_one, one_mul] at this
  linear_combination (-1 : R) * this

/-- The first-order deformation `φ + ε D : S → R[ε]` of `φ`. -/
def dualLift (φ : S →ₐ[k] R) (D : S →ₗ[k] R) (hD : IsDerivAlong φ D) :
    S →ₐ[k] TrivSqZeroExt R R where
  toFun a := inl (φ a) + inr (D a)
  map_one' := by simp [hD.map_one]
  map_mul' a b := by
    ext
    · simp
    · simp [hD a b]
      ring
  map_zero' := by simp
  map_add' a b := by
    ext <;> simp [add_comm]
  commutes' r := by
    ext <;> simp [Algebra.algebraMap_eq_smul_one, hD.map_one]

/-- The first component of `φ + ε D` is `φ`. -/
@[simp] theorem fst_dualLift (φ : S →ₐ[k] R) (D : S →ₗ[k] R) (hD : IsDerivAlong φ D) (a : S) :
    fst (dualLift φ D hD a) = φ a := by simp [dualLift]

/-- The `ε`-component of `φ + ε D` is `D`. -/
@[simp] theorem snd_dualLift (φ : S →ₐ[k] R) (D : S →ₗ[k] R) (hD : IsDerivAlong φ D) (a : S) :
    snd (dualLift φ D hD a) = D a := by simp [dualLift]

/-- The `ε`-component of a first-order deformation `g : S → R[ε]` of `φ`. -/
def sndOfLift (g : S →ₐ[k] TrivSqZeroExt R R) : S →ₗ[k] R where
  toFun a := snd (g a)
  map_add' a b := by simp
  map_smul' r a := by simp [snd_smul]

@[simp] theorem sndOfLift_apply (g : S →ₐ[k] TrivSqZeroExt R R) (a : S) :
    sndOfLift g a = snd (g a) := rfl

/-- The `ε`-component of a first-order deformation of `φ` is a derivation along `φ`. -/
theorem isDerivAlong_sndOfLift (φ : S →ₐ[k] R) (g : S →ₐ[k] TrivSqZeroExt R R)
    (hg : ∀ a, fst (g a) = φ a) : IsDerivAlong φ (sndOfLift g) := by
  intro a b
  simp [sndOfLift, hg, mul_comm]

/-- **First-order deformations are derivations**: the first-order lifts
`S → R[ε]` of `φ : S → R` correspond to the `k`-linear maps `D : S → R` with
`D (a b) = φ a · D b + φ b · D a`, i.e. the `k`-derivations of `S` into the `S`-module `R` (via
`φ`), i.e. `Hom_S(Ω_{S/k}, R)`. -/
def firstOrderLiftEquiv (φ : S →ₐ[k] R) :
    {D : S →ₗ[k] R // IsDerivAlong φ D} ≃
      {g : S →ₐ[k] TrivSqZeroExt R R // ∀ a, fst (g a) = φ a} where
  toFun D := ⟨dualLift φ D.1 D.2, fst_dualLift φ D.1 D.2⟩
  invFun g := ⟨sndOfLift g.1, isDerivAlong_sndOfLift φ g.1 g.2⟩
  left_inv D := by
    apply Subtype.ext; ext a; simp [sndOfLift]
  right_inv g := by
    apply Subtype.ext; ext a
    · simp [g.2 a]
    · simp [sndOfLift]

/-- A first-order deformation fixes `φ` on the closed subscheme cut out by the ideal `𝔟 ⊆ R`
(the marked points) iff the corresponding derivation takes values in `𝔟`, i.e. is a section of
`f^*T_U ⊗ 𝒪(-B)`: the `ε`-part of `g a` lies in `𝔟` for every `a`. -/
theorem snd_mem_iff_fixed (φ : S →ₐ[k] R) (𝔟 : Ideal R) (D : {D : S →ₗ[k] R // IsDerivAlong φ D}) :
    (∀ a, snd ((firstOrderLiftEquiv φ D).1 a) ∈ 𝔟) ↔ ∀ a, D.1 a ∈ 𝔟 := by
  simp [firstOrderLiftEquiv]

end FirstOrder

/-! ### Small extensions give square-zero thickenings of the curve -/

section SmallExtensionData

variable {k : Type u} [Field k] {A : ArtinLocalAlgebra k} (E : SmallExtension A)

/-- The kernel of a small extension is a square-zero ideal: it lies in the maximal ideal, which
kills it. -/
theorem SmallExtension.ker_mul_ker : RingHom.ker E.π.toRingHom * RingHom.ker E.π.toRingHom = ⊥ := by
  rw [eq_bot_iff, ← E.ker_mul_maximalIdeal]
  exact Ideal.mul_mono_right (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _))

/-- For a `k`-algebra `R` (the coordinate ring of an affine chart of `C`), the ideal
`J ⊗ R = ker (R ⊗ B → R ⊗ A)` of `R ⊗ B` is square-zero. -/
theorem SmallExtension.ker_tensor_mul_ker (R : Type*) [CommRing R] [Algebra k R] :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k R) E.π) *
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k R) E.π) = ⊥ := by
  have h : RingHom.ker E.π * RingHom.ker E.π = ⊥ := E.ker_mul_ker
  rw [Algebra.TensorProduct.lTensor_ker _ E.surjective, ← Ideal.map_mul, h, Ideal.map_bot]

/-- **Fixed values on the marked points**: if `K` is square-zero (e.g. `K = J ⊗ R`) then so is
`K ⊓ N` for every ideal `N` (e.g. `N = 𝔟 · (R ⊗ B)`, the ideal of the marked points in `C_B`),
which is the square-zero ideal of the lifting problem across `C_A ∪ B_{B}`. -/
theorem inf_mul_inf_eq_bot_of_mul_eq_bot {P : Type*} [CommSemiring P] {K : Ideal P}
    (hK : K * K = ⊥) (N : Ideal P) : (K ⊓ N) * (K ⊓ N) = ⊥ := by
  rw [eq_bot_iff, ← hK]
  exact Ideal.mul_mono inf_le_left inf_le_left

end SmallExtensionData

/-! ### Varying the target chart: restriction along formally étale chart maps -/

section Charted

set_option linter.style.haveILetI false

/-- **Lifting along a formally étale chart map**: let `σ : S → S'` be formally étale (an open
immersion of affine charts of the target), `I ⊆ P` square-zero, `ψ₀ : S → P` and `θ : S' → P/I`
compatible.  There is a unique `g : S' → P` with `g ∘ σ = ψ₀` lifting `θ`. -/
theorem existsUnique_lift_formallyEtale {k S S' P : Type*} [CommRing k] [CommRing S] [CommRing S']
    [CommRing P] [Algebra k S] [Algebra k S'] [Algebra k P] (σ : S →ₐ[k] S')
    (hσ : σ.toRingHom.FormallyEtale) (I : Ideal P) (hI : I * I = ⊥) (ψ0 : S →ₐ[k] P)
    (θ : S' →ₐ[k] P ⧸ I) (h : θ.comp σ = (Ideal.Quotient.mkₐ k I).comp ψ0) :
    ∃! g : S' →ₐ[k] P, g.comp σ = ψ0 ∧ (Ideal.Quotient.mkₐ k I).comp g = θ := by
  letI : Algebra S S' := σ.toRingHom.toAlgebra
  letI : Algebra S P := ψ0.toRingHom.toAlgebra
  haveI : Algebra.FormallyEtale S S' := hσ
  let θ' : S' →ₐ[S] P ⧸ I :=
    { θ.toRingHom with
      commutes' := fun a => congr($h a) }
  obtain ⟨hinj, hsurj⟩ := Algebra.FormallyEtale.comp_bijective S S' I ((pow_two I).trans hI)
  obtain ⟨g, hg⟩ := hsurj θ'
  have hcomm : ∀ r : k, g (algebraMap k S' r) = algebraMap k P r := by
    intro r
    have e1 : algebraMap k S' r = algebraMap S S' (algebraMap k S r) := (σ.commutes r).symm
    rw [e1, g.commutes]
    exact ψ0.commutes r
  let gk : S' →ₐ[k] P := { g.toRingHom with commutes' := hcomm }
  refine ⟨gk, ⟨?_, ?_⟩, ?_⟩
  · ext a; exact g.commutes a
  · ext a; exact congr($hg a)
  · rintro g2 ⟨h1, h2⟩
    let g2' : S' →ₐ[S] P :=
      { g2.toRingHom with
        commutes' := fun a => congr($h1 a) }
    have : g2' = g := by
      apply hinj
      ext a
      exact (congr($h2 a)).trans (congr($hg a)).symm
    ext a
    exact congr($this a)

variable {k : Type*} [CommRing k] {S S' P P' : Type*} [CommRing S] [CommRing S'] [CommRing P]
  [CommRing P'] [Algebra k S] [Algebra k S'] [Algebra k P] [Algebra k P']

/-- A morphism of thickening problems along a map of charts `σ : S → S'`: an algebra map
`ψ : P → P'` sending `I` into `I'` and carrying `φ` to `φ'` modulo the ideals, along `σ`. -/
structure ChartHom (σ : S →ₐ[k] S') (I : Ideal P) (φ : S →ₐ[k] P ⧸ I) (I' : Ideal P')
    (φ' : S' →ₐ[k] P' ⧸ I') where
  /-- The underlying algebra map. -/
  ψ : P →ₐ[k] P'
  mem : ∀ x ∈ I, ψ x ∈ I'
  compat : ∀ (a : S) (p : P), Ideal.Quotient.mk I p = φ a →
    Ideal.Quotient.mk I' (ψ p) = φ' (σ a)

namespace ChartHom

variable {σ : S →ₐ[k] S'} {I : Ideal P} {φ : S →ₐ[k] P ⧸ I} {I' : Ideal P'}
  {φ' : S' →ₐ[k] P' ⧸ I'} (h : ChartHom σ I φ I' φ')

/-- A lift of `φ'` is determined by its restriction along a formally étale `σ`. -/
theorem eq_of_comp_eq (hσ : σ.toRingHom.FormallyEtale) (hI' : I' * I' = ⊥)
    (g₁ g₂ : LiftsOf I' φ') (hg : ∀ a, g₁.1 (σ a) = g₂.1 (σ a)) : g₁ = g₂ := by
  have hc : φ'.comp σ = (Ideal.Quotient.mkₐ k I').comp (g₁.1.comp σ) := by
    ext a
    exact (g₁.mk_apply (σ a)).symm
  exact Subtype.ext <| (existsUnique_lift_formallyEtale σ hσ I' hI' (g₁.1.comp σ) φ' hc).unique
    ⟨rfl, g₁.2⟩ ⟨AlgHom.ext fun a => (hg a).symm, g₂.2⟩

/-- For a lift `g` of `φ`, `ψ ∘ g` lifts `φ' ∘ σ`. -/
theorem comp_eq (g : LiftsOf I φ) :
    φ'.comp σ = (Ideal.Quotient.mkₐ k I').comp (h.ψ.comp g.1) := by
  ext a
  exact (h.compat a (g.1 a) (g.mk_apply a)).symm

/-- The extension of a lift `g` of `φ` over `S` to the lift of `φ'` over `S'`
(`σ` formally étale): it is the unique lift of `φ'` restricting to `ψ ∘ g`. -/
def extLift (hσ : σ.toRingHom.FormallyEtale) (hI' : I' * I' = ⊥) (g : LiftsOf I φ) :
    LiftsOf I' φ' :=
  ⟨(existsUnique_lift_formallyEtale σ hσ I' hI' (h.ψ.comp g.1) φ' (h.comp_eq g)).exists.choose,
   (existsUnique_lift_formallyEtale σ hσ I' hI' (h.ψ.comp g.1) φ'
      (h.comp_eq g)).exists.choose_spec.2⟩

/-- The extension of `g` restricts along `σ` to `ψ ∘ g`. -/
theorem extLift_apply (hσ : σ.toRingHom.FormallyEtale) (hI' : I' * I' = ⊥) (g : LiftsOf I φ)
    (a : S) : (h.extLift hσ hI' g).1 (σ a) = h.ψ (g.1 a) :=
  congr($((existsUnique_lift_formallyEtale σ hσ I' hI' (h.ψ.comp g.1) φ'
    (h.comp_eq g)).exists.choose_spec.1) a)

/-- A lift of `φ'` restricting along `σ` to `ψ ∘ g` is the extension of `g`. -/
theorem extLift_unique (hσ : σ.toRingHom.FormallyEtale) (hI' : I' * I' = ⊥) (g : LiftsOf I φ)
    (g' : LiftsOf I' φ') (hg : ∀ a, g'.1 (σ a) = h.ψ (g.1 a)) : g' = h.extLift hσ hI' g :=
  eq_of_comp_eq hσ hI' _ _ fun a => (hg a).trans (h.extLift_apply hσ hI' g a).symm

variable [Algebra.FormallySmooth k S]

/-- The extension of a derivation along `φ` with values in `I` to the derivation along `φ'` with
values in `I'` (`σ` formally étale, `S` formally smooth): it is the difference of the extensions of
a lift and its translate. -/
def extDeriv (hσ : σ.toRingHom.FormallyEtale) (hI : I * I = ⊥) (hI' : I' * I' = ⊥)
    (D : Deriv I φ) : Deriv I' φ' :=
  letI g := (LiftsOf.nonempty hI φ).some
  (h.extLift hσ hI' (g.add hI D)).sub hI' (h.extLift hσ hI' g)

/-- The extension of `D` restricts along `σ` to `ψ ∘ D`. -/
theorem extDeriv_apply (hσ : σ.toRingHom.FormallyEtale) (hI : I * I = ⊥) (hI' : I' * I' = ⊥)
    (D : Deriv I φ) (a : S) :
    (((h.extDeriv hσ hI hI' D).1 (σ a) : I') : P') = h.ψ ((D.1 a : I) : P) := by
  simp only [extDeriv, LiftsOf.sub_apply, extLift_apply, LiftsOf.add_apply, map_add]
  ring

/-- A derivation along `φ'` restricting along `σ` to `ψ ∘ D` is the extension of `D`. -/
theorem extDeriv_unique (hσ : σ.toRingHom.FormallyEtale) (hI : I * I = ⊥) (hI' : I' * I' = ⊥)
    (D : Deriv I φ) (E : Deriv I' φ')
    (hE : ∀ a, ((E.1 (σ a) : I') : P') = h.ψ ((D.1 a : I) : P)) :
    E = h.extDeriv hσ hI hI' D := by
  letI g := (LiftsOf.nonempty hI φ).some
  have key : (h.extLift hσ hI' g).add hI' E = (h.extLift hσ hI' g).add hI'
      (h.extDeriv hσ hI hI' D) :=
    eq_of_comp_eq hσ hI' _ _ fun a => by
      simp only [LiftsOf.add_apply, extLift_apply, hE, extDeriv_apply]
  have := congrArg (fun x => x.sub hI' (h.extLift hσ hI' g)) key
  simpa only [LiftsOf.add_sub_cancel] using this

/-- The extension of `g + D` is the extension of `g` translated by the extension of `D`. -/
theorem extLift_add (hσ : σ.toRingHom.FormallyEtale) (hI : I * I = ⊥) (hI' : I' * I' = ⊥)
    (g : LiftsOf I φ) (D : Deriv I φ) :
    h.extLift hσ hI' (g.add hI D) = (h.extLift hσ hI' g).add hI' (h.extDeriv hσ hI hI' D) :=
  (eq_of_comp_eq hσ hI' _ _ fun a => by
    simp only [LiftsOf.add_apply, extLift_apply, extDeriv_apply, map_add]).symm

/-- `extDeriv` as a `k`-linear map. -/
def extDerivₗ (hσ : σ.toRingHom.FormallyEtale) (hI : I * I = ⊥) (hI' : I' * I' = ⊥) :
    Deriv I φ →ₗ[k] Deriv I' φ' where
  toFun := h.extDeriv hσ hI hI'
  map_add' D E := (h.extDeriv_unique hσ hI hI' (D + E) (h.extDeriv hσ hI hI' D +
    h.extDeriv hσ hI hI' E) (fun a => by
      simp [extDeriv_apply])).symm
  map_smul' c D := (h.extDeriv_unique hσ hI hI' (c • D) (c • h.extDeriv hσ hI hI' D)
    (fun a => by
      simp [extDeriv_apply])).symm

end ChartHom

/-! ### The charted Čech torsor of local lifts -/

section ChartedLiftCover

/-- The target charts of a multi-chart lifting problem over a cover: for each intersection `U_s`
of members of the cover an affine chart `Spec (S s)` of the (smooth) target containing the image of
`U_s`, the chart maps `S s → S t` (`s ⊆ t`) being formally étale (inclusions of affine open charts;
the common chart of `U_ij` is `W_i ∩ W_j`, affine as the target is separated). -/
structure ChartData (k : Type*) [CommRing k] (ι : Type*) where
  /-- The coordinate rings of the target charts. -/
  S : Finset ι → Type v
  [commRing_S : ∀ s, CommRing (S s)]
  [algebra_S : ∀ s, Algebra k (S s)]
  /-- The target charts are smooth over `k`. -/
  smooth : ∀ s, Algebra.FormallySmooth k (S s)
  /-- The inclusions of charts. -/
  σ : ∀ {s t : Finset ι}, s ⊆ t → S s →ₐ[k] S t
  σ_refl : ∀ {s : Finset ι} (h : s ⊆ s) (x : S s), σ h x = x
  σ_comp : ∀ {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : S s),
    σ h₂ (σ h₁ x) = σ (h₁.trans h₂) x
  formallyEtale : ∀ {s t : Finset ι} (h : s ⊆ t), (σ h).toRingHom.FormallyEtale

attribute [instance] ChartData.commRing_S ChartData.algebra_S ChartData.smooth

/-- The data of a lifting problem over a cover, with varying target charts `W`: the rings `P s` of
sections of `𝒪` of `C_{A'}` over `U_s`, square-zero ideals `I s`, and maps `φ s : S s → P s / I s`
compatible with restriction through the chart maps; the restriction of lifts compares two lifts
on `U_ij` through the common chart. -/
structure ChartedLiftCover {k : Type*} [CommRing k] {ι : Type*} (W : ChartData.{v} k ι) where
  /-- The rings of sections over `U_s`. -/
  P : Finset ι → Type v
  [commRing_P : ∀ s, CommRing (P s)]
  [algebra_P : ∀ s, Algebra k (P s)]
  /-- The square-zero ideals. -/
  I : ∀ s, Ideal (P s)
  hI : ∀ s, I s * I s = ⊥
  /-- The given maps. -/
  φ : ∀ s, W.S s →ₐ[k] P s ⧸ I s
  /-- Restriction. -/
  hom : ∀ {s t : Finset ι} (h : s ⊆ t), ChartHom (W.σ h) (I s) (φ s) (I t) (φ t)
  hom_refl : ∀ {s : Finset ι} (h : s ⊆ s) (x : P s), (hom h).ψ x = x
  hom_comp : ∀ {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : P s),
    (hom h₂).ψ ((hom h₁).ψ x) = (hom (h₁.trans h₂)).ψ x

namespace ChartedLiftCover

attribute [instance] commRing_P algebra_P

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι] {W : ChartData.{v} k ι}
  (C : ChartedLiftCover W)

/-- Extending a derivation along the identity of `U_s` leaves it unchanged. -/
theorem extDeriv_refl {s : Finset ι} (h : s ⊆ s) (x : Deriv (C.I s) (C.φ s)) :
    (C.hom h).extDeriv (W.formallyEtale h) (C.hI s) (C.hI s) x = x :=
  ((C.hom h).extDeriv_unique (W.formallyEtale h) (C.hI s) (C.hI s) x x
    (fun a => by rw [W.σ_refl, C.hom_refl])).symm

/-- Extension of derivations is compatible with composition of inclusions `s ⊆ t ⊆ u`. -/
theorem extDeriv_comp {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : Deriv (C.I s) (C.φ s)) :
    (C.hom h₂).extDeriv (W.formallyEtale h₂) (C.hI t) (C.hI u)
      ((C.hom h₁).extDeriv (W.formallyEtale h₁) (C.hI s) (C.hI t) x) =
    (C.hom (h₁.trans h₂)).extDeriv (W.formallyEtale (h₁.trans h₂)) (C.hI s) (C.hI u) x := by
  refine (C.hom (h₁.trans h₂)).extDeriv_unique (W.formallyEtale (h₁.trans h₂)) (C.hI s)
    (C.hI u) x _ (fun a => ?_)
  rw [← W.σ_comp h₁ h₂, ChartHom.extDeriv_apply, ChartHom.extDeriv_apply, C.hom_comp]

/-- Extending a lift along the identity of `U_s` leaves it unchanged. -/
theorem extLift_refl {s : Finset ι} (h : s ⊆ s) (x : LiftsOf (C.I s) (C.φ s)) :
    (C.hom h).extLift (W.formallyEtale h) (C.hI s) x = x :=
  ((C.hom h).extLift_unique (W.formallyEtale h) (C.hI s) x x
    (fun a => by rw [W.σ_refl, C.hom_refl])).symm

/-- Extension of lifts is compatible with composition of inclusions `s ⊆ t ⊆ u`. -/
theorem extLift_comp {s t u : Finset ι} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : LiftsOf (C.I s) (C.φ s)) :
    (C.hom h₂).extLift (W.formallyEtale h₂) (C.hI u)
      ((C.hom h₁).extLift (W.formallyEtale h₁) (C.hI t) x) =
    (C.hom (h₁.trans h₂)).extLift (W.formallyEtale (h₁.trans h₂)) (C.hI u) x := by
  refine (C.hom (h₁.trans h₂)).extLift_unique (W.formallyEtale (h₁.trans h₂)) (C.hI u)
    x _ (fun a => ?_)
  rw [← W.σ_comp h₁ h₂, ChartHom.extLift_apply, ChartHom.extLift_apply, C.hom_comp]

/-- The presheaf of derivations `S_s → I_s` along `φ_s`: `Γ(U_s, f^*T_U ⊗ J)`. -/
def derivPresheaf : CechPresheaf.{v} k ι where
  obj s := Deriv (C.I s) (C.φ s)
  res h := (C.hom h).extDerivₗ (W.formallyEtale h) (C.hI _) (C.hI _)
  res_refl h x := C.extDeriv_refl h x
  res_comp h₁ h₂ x := C.extDeriv_comp h₁ h₂ x

/-- The pseudo-torsor of local lifts of `φ_s` to `P s`, under the derivations. -/
def liftTorsor : CechTorsor C.derivPresheaf where
  X s := LiftsOf (C.I s) (C.φ s)
  res h := (C.hom h).extLift (W.formallyEtale h) (C.hI _)
  res_refl h x := C.extLift_refl h x
  res_comp h₁ h₂ x := C.extLift_comp h₁ h₂ x
  vadd s D g := g.add (C.hI s) D
  vsub s g₁ g₂ := g₁.sub (C.hI s) g₂
  vadd_zero s x := x.add_zero (C.hI s)
  vadd_add s D E x :=
    (congrArg (LiftsOf.add (C.hI s) x) (add_comm D E)).trans (LiftsOf.add_add (C.hI s) x E D).symm
  vsub_vadd s x y := LiftsOf.sub_add_cancel (C.hI s) x y
  vadd_vsub s D y := LiftsOf.add_sub_cancel (C.hI s) y D
  res_vadd h D x := (C.hom h).extLift_add (W.formallyEtale h) (C.hI _) (C.hI _) x D

/-- **First obstruction** (multi-chart form, independent of the choice of local lifts): the Čech
class in `Ȟ¹(𝔘, 𝒟)` of the differences of local lifts, compared on `U_ij` through the common
chart `W_i ∩ W_j`. -/
def firstObstruction (x : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i})) : C.derivPresheaf.H1 :=
  C.liftTorsor.obstruction x

/-- The first obstruction does not depend on the family of local lifts chosen. -/
theorem firstObstruction_eq (x y : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i})) :
    C.firstObstruction x = C.firstObstruction y :=
  C.liftTorsor.obstruction_eq x y

/-- The first obstruction vanishes iff the local lifts can be modified, by derivations on the
`U_i`, to a compatible family of local lifts (compatible through the common charts). -/
theorem firstObstruction_eq_zero_iff (x : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i})) :
    C.firstObstruction x = 0 ↔ ∃ y : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i}), ∀ i j : ι,
      C.liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
        C.liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j) :=
  C.liftTorsor.obstruction_eq_zero_iff x

/-- Smooth lifting: the local lifts exist over each `U_i`. -/
theorem nonempty_liftsOf (s : Finset ι) : Nonempty (LiftsOf (C.I s) (C.φ s)) :=
  LiftsOf.nonempty (C.hI s) (C.φ s)

section Base

variable {k : Type v} [CommRing k] {ι : Type*} {W : ChartData.{v} k ι} (C : ChartedLiftCover W)

/-- A morphism of thickenings over the base `S = k`: any algebra map sending `I` into `I'`. -/
def _root_.MMP.Fourfold.SqZeroHom.ofBase {P P' : Type v} [CommRing P] [CommRing P'] [Algebra k P]
    [Algebra k P'] (I : Ideal P) (I' : Ideal P') (ψ : P →ₐ[k] P') (mem : ∀ x ∈ I, ψ x ∈ I') :
    SqZeroHom I (Algebra.ofId k (P ⧸ I)) I' (Algebra.ofId k (P' ⧸ I')) where
  ψ := ψ
  mem := mem
  compat a p hp := by
    have hp' : p - algebraMap k P a ∈ I := by
      rw [← Ideal.Quotient.eq]; simpa using hp
    have := mem _ hp'
    rw [map_sub, AlgHom.commutes, ← Ideal.Quotient.eq] at this
    simpa using this

/-- The underlying single-chart problem forgetting the target (`S = k`): it carries the
second obstruction, which does not depend on the charts. -/
def toLiftCover : LiftCover.{v} k k ι where
  P := C.P
  I := C.I
  hI := C.hI
  φ s := Algebra.ofId k _
  hom h := SqZeroHom.ofBase _ _ (C.hom h).ψ (C.hom h).mem
  hom_refl := C.hom_refl
  hom_comp := C.hom_comp

end Base

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι] {W : ChartData.{v} k ι}
  {C C' : ChartedLiftCover W}

/-- A morphism of multi-chart lifting problems over the same charts (in the application, the
quotient of the extension by a subspace of `J`). -/
structure Hom (C C' : ChartedLiftCover W) where
  /-- The component maps. -/
  sq : ∀ s, SqZeroHom (C.I s) (C.φ s) (C'.I s) (C'.φ s)
  comm : ∀ {s t : Finset ι} (h : s ⊆ t) (x : C.P s),
    (sq t).ψ ((C.hom h).ψ x) = (C'.hom h).ψ ((sq s).ψ x)

variable (m : Hom C C')

/-- The induced morphism of presheaves of derivations. -/
def Hom.derivHom : C.derivPresheaf.Hom C'.derivPresheaf where
  map s := (m.sq s).mapDerivₗ (C'.hI s)
  map_res {s t} h x :=
    (C'.hom h).extDeriv_unique (W.formallyEtale h) (C'.hI s) (C'.hI t) _ _ (fun a => by
      have e := (C.hom h).extDeriv_apply (W.formallyEtale h) (C.hI s) (C.hI t)
        (x : Deriv (C.I s) (C.φ s)) a
      change (m.sq t).ψ ((((C.hom h).extDeriv (W.formallyEtale h) (C.hI s) (C.hI t)
        (x : Deriv (C.I s) (C.φ s))).1 (W.σ h a) : C.I t) : C.P t) = _
      rw [e, m.comm]
      rfl)

/-- The induced morphism of torsors of local lifts. -/
def Hom.liftHom : C.liftTorsor.Hom C'.liftTorsor m.derivHom where
  map s := (m.sq s).mapLift
  map_res {s t} h x :=
    (C'.hom h).extLift_unique (W.formallyEtale h) (C'.hI t) _ _ (fun a => by
      have e := (C.hom h).extLift_apply (W.formallyEtale h) (C.hI t)
        (x : LiftsOf (C.I s) (C.φ s)) a
      change (m.sq t).ψ (((C.hom h).extLift (W.formallyEtale h) (C.hI t)
        (x : LiftsOf (C.I s) (C.φ s))).1 (W.σ h a)) = _
      rw [e, m.comm]
      rfl)
  map_vadd s D x := (m.sq s).mapLift_add (C.hI s) (C'.hI s) x D

/-- **Naturality of the first obstruction** (multi-chart form) under a morphism of lifting
problems. -/
theorem Hom.firstObstruction_map (x : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i})) :
    m.derivHom.h1 (C.firstObstruction x) =
      C'.firstObstruction (fun i => (m.sq _).mapLift (x i)) :=
  m.liftHom.obstruction_map x

/-- The morphism of underlying single-chart problems. -/
def Hom.toLiftCover {k : Type v} [CommRing k] {W : ChartData.{v} k ι} {C C' : ChartedLiftCover W}
    (m : Hom C C') : C.toLiftCover.Hom C'.toLiftCover where
  sq s := SqZeroHom.ofBase _ _ (m.sq s).ψ (m.sq s).mem
  comm := m.comm

end ChartedLiftCover

end ChartedLiftCover

end Charted

/-! ### Packaging: a two-stage obstruction theory from Čech data -/

section Packaging

open TensorProduct

namespace ChartedLiftCover

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι] {W : ChartData.{v} k ι}
  (C : ChartedLiftCover W)

/-- A compatible family of local lifts over the cover: lifts `y_i` over the `U_i` whose
restrictions to every `U_ij` (through the common chart) agree; by gluing of morphisms of
schemes this is a map `C_{A'} → U` lifting the given one. -/
def Compat : Type _ :=
  {y : ∀ i : ι, LiftsOf (C.I {i}) (C.φ {i}) //
    ∀ i j : ι, C.liftTorsor.res (CechPresheaf.sub_pair_left i j) (y i) =
      C.liftTorsor.res (CechPresheaf.sub_pair_right i j) (y j)}

variable {C} {C' : ChartedLiftCover W}

/-- A morphism of lifting problems carries compatible families to compatible families. -/
def Hom.mapCompat (m : Hom C C') (y : C.Compat) : C'.Compat :=
  ⟨fun i => (m.sq _).mapLift (y.1 i), fun i j => by
    have h₁ := m.liftHom.map_res (CechPresheaf.sub_pair_left i j) (y.1 i)
    have h₂ := m.liftHom.map_res (CechPresheaf.sub_pair_right i j) (y.1 j)
    exact h₁.symm.trans ((congrArg (m.liftHom.map _) (y.2 i j)).trans h₂)⟩

end ChartedLiftCover

/-- The second obstruction depends only on the two systems of transition functions. -/
theorem LiftCover.secondObstruction_congr {k : Type*} [CommRing k] {S : Type v} [CommRing S]
    [Algebra k S] {ι : Type*} [DecidableEq ι] (C : LiftCover.{v} k S ι)
    {g₁ g₂ g₁' g₂' : ∀ i j : ι, (C.P {i, j})ˣ} (h : g₁ = g₂) (h' : g₁' = g₂')
    (hg₁ : C.IsUnitCocycle g₁) (hg₁' : C.IsUnitCocycle g₁')
    (hc₁ : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g₁' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g₁ i j : C.P {i, j}))
    (hg₂ : C.IsUnitCocycle g₂) (hg₂' : C.IsUnitCocycle g₂')
    (hc₂ : ∀ i j, Ideal.Quotient.mk (C.I {i, j}) (g₂' i j : C.P {i, j}) =
      Ideal.Quotient.mk (C.I {i, j}) (g₂ i j : C.P {i, j})) :
    C.secondObstruction hg₁ hg₁' hc₁ = C.secondObstruction hg₂ hg₂' hc₂ := by
  subst h h'
  rfl

/-- **The Čech data of a family of curve maps over Artinian bases.**  `R` is the local ring of the
coefficient space `M` at `[f]`, so that `R → A` is a map `C_A → U` fixing `B` with pullback line
bundle isomorphic to `L_A` (normalised), and the data for a small extension `E` of `A` and such a
point `a` are:

* `cover E a`: the multi-chart lifting problem (affine charts `W` of `U`, sections `P_s` of
  `C_{A'}` over the intersections of the cover, ideals `I_s = J ⊗ 𝔟` of the sections vanishing
  over `C_A`/the marked points), with `coverMap` its functoriality in the quotients of `J`;
* `θ₁`: the identification of the Čech `H¹` of the presheaf of derivations
  (`f^*T_U(-B) ⊗ J`) with `V₁ ⊗ J`, `V₁ = H¹(C, f^*T_U(-B))`, natural in `J`;
* `θ₂`: that of the Čech `H¹` of the ideals (`𝒪_C ⊗ J`) with `V₂ ⊗ J`, `V₂ = H¹(C, 𝒪_C)`;
* `ref`, `pull`: the transition functions of the fixed line bundle `L_{A'}`, resp. of the
  pull-back of `𝒪(1)` along the glued lift, which agree over `A` (the given isomorphism), with
  their naturality;
* `lift_of_iso`: the universal property of `M`: a glued lift whose pull-back line bundle is
  isomorphic to `L_{A'}` over the identity modulo `J` is an `A'`-point of `M`. -/
structure CurveDeformationData (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    {ι : Type} [DecidableEq ι] (W : ChartData.{u} k ι) (V₁ V₂ : Type u)
    [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] where
  /-- The lifting problem over the cover of `C_{A'}` determined by the small extension `E` and
    the point `a`. -/
  cover : ∀ {A : ArtinLocalAlgebra k}, SmallExtension A → (R →ₐ[k] A.carrier) →
    ChartedLiftCover W
  /-- The morphism of lifting problems induced by a map of small extensions of `A`. -/
  coverMap : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A}, E.QuotientMap E' →
    ∀ (a : R →ₐ[k] A.carrier), (cover E a).Hom (cover E' a)
  /-- The identification of the Čech `H¹` of the derivation presheaf with `V₁ ⊗ J`. -/
  θ₁ : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier),
    (cover E a).derivPresheaf.H1 ≃ₗ[k] V₁ ⊗[k] E.kernel
  /-- `θ₁` is natural in the small extension. -/
  θ₁_map : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    (a : R →ₐ[k] A.carrier) (z : (cover E a).derivPresheaf.H1),
    θ₁ E' a ((coverMap q a).derivHom.h1 z) = LinearMap.lTensor V₁ q.kerMap (θ₁ E a z)
  /-- The identification of the Čech `H¹` of the ideal presheaf with `V₂ ⊗ J`. -/
  θ₂ : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier),
    (cover E a).toLiftCover.idealPresheaf.H1 ≃ₗ[k] V₂ ⊗[k] E.kernel
  /-- `θ₂` is natural in the small extension. -/
  θ₂_map : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    (a : R →ₐ[k] A.carrier) (z : (cover E a).toLiftCover.idealPresheaf.H1),
    θ₂ E' a ((coverMap q a).toLiftCover.idealHom.h1 z) = LinearMap.lTensor V₂ q.kerMap (θ₂ E a z)
  /-- The transition functions of the fixed line bundle `L_{A'}` on the cover. -/
  ref : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier) (i j : ι),
    ((cover E a).toLiftCover.P {i, j})ˣ
  /-- The transition functions `ref E a` form a unit cocycle. -/
  isUnitCocycle_ref : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A)
    (a : R →ₐ[k] A.carrier), (cover E a).toLiftCover.IsUnitCocycle (ref E a)
  /-- The transition functions of the pull-back of `𝒪(1)` along the lift glued from a compatible
    family. -/
  pull : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier)
    (_ : (cover E a).Compat) (i j : ι), ((cover E a).toLiftCover.P {i, j})ˣ
  /-- The transition functions `pull E a y` form a unit cocycle. -/
  isUnitCocycle_pull : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A)
    (a : R →ₐ[k] A.carrier) (y : (cover E a).Compat),
    (cover E a).toLiftCover.IsUnitCocycle (pull E a y)
  /-- Modulo the ideals, `pull E a y` agrees with `ref E a`. -/
  mk_pull : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier)
    (y : (cover E a).Compat) (i j : ι),
    Ideal.Quotient.mk ((cover E a).toLiftCover.I {i, j}) ((pull E a y i j : _) :
      (cover E a).toLiftCover.P {i, j}) =
    Ideal.Quotient.mk ((cover E a).toLiftCover.I {i, j}) ((ref E a i j : _) :
      (cover E a).toLiftCover.P {i, j})
  /-- `ref` is natural in the small extension. -/
  mapUnit_ref : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    (a : R →ₐ[k] A.carrier) (i j : ι),
    (coverMap q a).toLiftCover.mapUnit {i, j} (ref E a i j) = ref E' a i j
  /-- `pull` is natural in the small extension. -/
  mapUnit_pull : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    (a : R →ₐ[k] A.carrier) (y : (cover E a).Compat) (i j : ι),
    (coverMap q a).toLiftCover.mapUnit {i, j} (pull E a y i j) =
      pull E' a ((coverMap q a).mapCompat y) i j
  /-- A compatible family whose pulled-back line bundle is isomorphic to `L_{A'}`, by an
    isomorphism that is the identity modulo `J`, comes from a lift of `a` to `E.big`. -/
  lift_of_iso : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier)
    (y : (cover E a).Compat),
    (∃ e : ∀ i : ι, ((cover E a).toLiftCover.P {i})ˣ,
      (∀ i, Ideal.Quotient.mk ((cover E a).toLiftCover.I {i}) (e i : _) = 1) ∧
      ∀ i j : ι, pull E a y i j * (cover E a).toLiftCover.resUnit
          (CechPresheaf.sub_pair_left i j) (e i) =
        (cover E a).toLiftCover.resUnit (CechPresheaf.sub_pair_right i j) (e j) * ref E a i j) →
    ∃ b : R →ₐ[k] E.big.carrier, E.π.comp b = a

namespace CurveDeformationData

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R] {ι : Type}
  [DecidableEq ι] {W : ChartData.{u} k ι} {V₁ V₂ : Type u} [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] (D : CurveDeformationData k R W V₁ V₂)

/-- Chosen local lifts over the `U_i` (smooth lifting). -/
def localLift {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier)
    (i : ι) : LiftsOf ((D.cover E a).I {i}) ((D.cover E a).φ {i}) :=
  ((D.cover E a).nonempty_liftsOf {i}).some

/-- The first obstruction of the point `a` along `E`: the Čech class of the differences of any
local lifts, in `V₁ ⊗ J`. -/
def obs₁ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier) :
    V₁ ⊗[k] E.kernel :=
  D.θ₁ E a ((D.cover E a).firstObstruction (D.localLift E a))

/-- The second obstruction of a compatible family of local lifts, in `V₂ ⊗ J`. -/
def obs₂ {A : ArtinLocalAlgebra k} {E : SmallExtension A} {a : R →ₐ[k] A.carrier}
    (y : (D.cover E a).Compat) : V₂ ⊗[k] E.kernel :=
  D.θ₂ E a ((D.cover E a).toLiftCover.secondObstruction (D.isUnitCocycle_ref E a)
    (D.isUnitCocycle_pull E a y) (D.mk_pull E a y))

/-- Naturality of the first obstruction in the quotient maps of small extensions. -/
theorem obs₁_map {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    (a : R →ₐ[k] A.carrier) :
    D.obs₁ E' a = LinearMap.lTensor V₁ q.kerMap (D.obs₁ E a) := by
  unfold obs₁
  rw [← D.θ₁_map q a, (D.coverMap q a).firstObstruction_map]
  exact congrArg _ (ChartedLiftCover.firstObstruction_eq _ _ _)

/-- Naturality of the second obstruction in the quotient maps of small extensions. -/
theorem obs₂_map {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    {a : R →ₐ[k] A.carrier} (y : (D.cover E a).Compat) :
    D.obs₂ ((D.coverMap q a).mapCompat y) = LinearMap.lTensor V₂ q.kerMap (D.obs₂ y) := by
  unfold obs₂
  rw [← D.θ₂_map q a, LiftCover.Hom.secondObstruction_map]
  refine congrArg _ (LiftCover.secondObstruction_congr _ ?_ ?_ _ _ _ _ _ _)
  · funext i j; exact (D.mapUnit_ref q a i j).symm
  · funext i j; exact (D.mapUnit_pull q a y i j).symm

/-- **The two-stage obstruction theory of curve maps.** -/
def toTheory : TwoStageObstructionTheory.{u, u, u} k R V₁ V₂ where
  Intermediate E a := (D.cover E a).Compat
  obs₁ E a := D.obs₁ E a
  obs₂ y := D.obs₂ y
  exists_intermediate E a h := by
    have h0 : (D.cover E a).firstObstruction (D.localLift E a) = 0 :=
      (D.θ₁ E a).injective (by rw [map_zero]; exact h)
    obtain ⟨y, hy⟩ := ((D.cover E a).firstObstruction_eq_zero_iff _).1 h0
    exact ⟨⟨y, hy⟩⟩
  exists_lift E a y h := by
    have h0 : (D.cover E a).toLiftCover.secondObstruction (D.isUnitCocycle_ref E a)
        (D.isUnitCocycle_pull E a y) (D.mk_pull E a y) = 0 :=
      (D.θ₂ E a).injective (by rw [map_zero]; exact h)
    exact D.lift_of_iso E a y
      ((D.cover E a).toLiftCover.exists_iso_of_secondObstruction_eq_zero _ _ _ h0)
  mapIntermediate := fun {A} {E} {E'} q {a} y => (D.coverMap q a).mapCompat y
  obs₁_map q a := D.obs₁_map q a
  obs₂_map := fun {A} {E} {E'} q {a} y => D.obs₂_map q y

end CurveDeformationData

end Packaging

/-! ### Gluing compatible local lifts to a morphism of schemes -/

section SchemeGluing

open AlgebraicGeometry CategoryTheory Limits

namespace ChartedLiftCover

variable {k : Type v} [CommRing k] {X Y : Scheme.{v}} (𝒰 : X.OpenCover)
  [DecidableEq 𝒰.I₀] {W : ChartData.{v} k 𝒰.I₀}

/-- Restriction of a local lift commutes with the chart maps, at the level of schemes. -/
theorem spec_res_eq (C : ChartedLiftCover W) {s t : Finset 𝒰.I₀} (h : s ⊆ t)
    (w : ∀ s : Finset 𝒰.I₀, Spec (CommRingCat.of (W.S s)) ⟶ Y)
    (hw : ∀ {s t : Finset 𝒰.I₀} (h : s ⊆ t),
      Spec.map (CommRingCat.ofHom (W.σ h).toRingHom) ≫ w s = w t)
    (g : LiftsOf (C.I s) (C.φ s)) :
    Spec.map (CommRingCat.ofHom (C.hom h).ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.1.toRingHom) ≫ w s =
      Spec.map (CommRingCat.ofHom (C.liftTorsor.res h g).1.toRingHom) ≫ w t := by
  have hring : CommRingCat.ofHom g.1.toRingHom ≫ CommRingCat.ofHom (C.hom h).ψ.toRingHom =
      CommRingCat.ofHom (W.σ h).toRingHom ≫
        CommRingCat.ofHom (C.liftTorsor.res h g).1.toRingHom := by
    ext a
    exact ((C.hom h).extLift_apply (W.formallyEtale h) (C.hI _) g a).symm
  rw [← Category.assoc, ← Spec.map_comp, hring, Spec.map_comp, Category.assoc, hw]

/-- **Gluing of compatible local lifts.**  Let `𝒰` be an open cover of the scheme `X`
(the thickened curve `C_{A'}`) by affine opens `𝒰.X i ≅ Spec (P {i})` whose pairwise intersections
`𝒰.X i ×_X 𝒰.X j ≅ Spec (P {i, j})` are affine with the restriction maps `P {i} → P {i, j}`,
`W {s}` the target charts, `w s : Spec (S s) → Y` the chart inclusions into the target `Y = U`,
compatible with the chart maps.  A compatible family of local lifts glues to a morphism
`X → Y` whose restriction to `𝒰.X i` is the composite of the local lift with the chart. -/
theorem exists_glue (C : ChartedLiftCover W)
    (α : ∀ i, 𝒰.X i ≅ Spec (CommRingCat.of (C.P {i})))
    (β : ∀ i j, pullback (𝒰.f i) (𝒰.f j) ≅ Spec (CommRingCat.of (C.P {i, j})))
    (hβ₁ : ∀ i j, (β i j).hom ≫ Spec.map (CommRingCat.ofHom
      (C.hom (CechPresheaf.sub_pair_left i j)).ψ.toRingHom) = pullback.fst _ _ ≫ (α i).hom)
    (hβ₂ : ∀ i j, (β i j).hom ≫ Spec.map (CommRingCat.ofHom
      (C.hom (CechPresheaf.sub_pair_right i j)).ψ.toRingHom) = pullback.snd _ _ ≫ (α j).hom)
    (w : ∀ s : Finset 𝒰.I₀, Spec (CommRingCat.of (W.S s)) ⟶ Y)
    (hw : ∀ {s t : Finset 𝒰.I₀} (h : s ⊆ t),
      Spec.map (CommRingCat.ofHom (W.σ h).toRingHom) ≫ w s = w t)
    (y : C.Compat) :
    ∃ g : X ⟶ Y, ∀ i, 𝒰.f i ≫ g =
      (α i).hom ≫ Spec.map (CommRingCat.ofHom (y.1 i).1.toRingHom) ≫ w {i} := by
  have key : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (α i).hom ≫
      Spec.map (CommRingCat.ofHom (y.1 i).1.toRingHom) ≫ w {i} =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (α j).hom ≫
        Spec.map (CommRingCat.ofHom (y.1 j).1.toRingHom) ≫ w {j} := by
    intro i j
    have e₁ : pullback.fst (𝒰.f i) (𝒰.f j) ≫ (α i).hom ≫
        Spec.map (CommRingCat.ofHom (y.1 i).1.toRingHom) ≫ w {i} =
        (β i j).hom ≫ Spec.map (CommRingCat.ofHom
          (C.liftTorsor.res (CechPresheaf.sub_pair_left i j) (y.1 i)).1.toRingHom) ≫
          w {i, j} := by
      rw [← Category.assoc (pullback.fst _ _) (α i).hom, ← hβ₁, Category.assoc,
        C.spec_res_eq 𝒰 (CechPresheaf.sub_pair_left i j) w hw (y.1 i)]
    have e₂ : pullback.snd (𝒰.f i) (𝒰.f j) ≫ (α j).hom ≫
        Spec.map (CommRingCat.ofHom (y.1 j).1.toRingHom) ≫ w {j} =
        (β i j).hom ≫ Spec.map (CommRingCat.ofHom
          (C.liftTorsor.res (CechPresheaf.sub_pair_right i j) (y.1 j)).1.toRingHom) ≫
          w {i, j} := by
      rw [← Category.assoc (pullback.snd _ _) (α j).hom, ← hβ₂, Category.assoc,
        C.spec_res_eq 𝒰 (CechPresheaf.sub_pair_right i j) w hw (y.1 j)]
    rw [e₁, e₂, y.2 i j]
  exact ⟨𝒰.glueMorphisms _ key, fun i => 𝒰.ι_glueMorphisms _ key i⟩

end ChartedLiftCover

end SchemeGluing

end MMP.Fourfold
