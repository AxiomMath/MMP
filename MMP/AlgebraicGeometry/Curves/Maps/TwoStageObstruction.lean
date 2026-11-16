module

public import MMP.Attr
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import StacksFrontier.RingTheory.MvPowerSeries.KrullDimension
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.ResidueFieldAffineChart.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.SectionPoint

/-!
# A local dimension bound from two successive obstruction spaces

Let `M` be a scheme locally of finite type over a field `k` and `x ∈ M(k)` a rational point, with
local ring `R = 𝒪_{M,x}`. The `M`-points of `Spec A` lying over `x`, for a local Artinian
`k`-algebra `A` with residue field `k`, are the `k`-algebra homomorphisms `R → A`. A *two-stage
obstruction theory* with obstruction spaces `V₁`, `V₂` solves every lifting problem along a small
extension `B → A` with kernel `J` (killed by the maximal ideal of `B`): the first obstruction lies
in `V₁ ⊗ J`; when it vanishes an intermediate lift exists, and each has a second obstruction in
`V₂ ⊗ J`; when that vanishes the point lifts to `B`. The obstructions and the intermediate lifts are
compatible with quotienting `J`.

If such a theory exists, then `dim_x M ≥ dim_k T_x M - dim V₁ - dim V₂`.

The proof follows the classical argument: `R̂ ≅ k[[z₁,…,zₜ]]/I` with `I ⊆ 𝔪²`; the extension
`k[[z]]/(𝔪I + 𝔪ᴺ) → R/𝔪ᴺ` is cut down by a subspace of the kernel of dimension `≤ dim V₁`, then
by one of dimension `≤ dim V₂`, until both obstructions vanish; a lift of the canonical point
differs from the canonical map by kernel elements, which do not change the value of an element of
`𝔪²` since the maximal ideal kills the kernel; hence `I` is contained in the subspace cut out,
Nakayama bounds the number of generators of `I` by `dim V₁ + dim V₂`, and Krull's height theorem
bounds `dim R̂ = dim R`.

## Main definitions

* `MMP.Fourfold.ArtinLocalAlgebra`: a local Artinian `k`-algebra with residue field `k`.
* `MMP.Fourfold.SmallExtension`: a small extension of such an algebra, with its kernel
  `MMP.Fourfold.SmallExtension.kernel` and quotient maps `MMP.Fourfold.SmallExtension.QuotientMap`.
* `MMP.Fourfold.TwoStageObstructionTheory`: the two-stage obstruction theory at a `k`-point.

## Main results

* `MMP.Fourfold.natCast_finrank_cotangentSpace_le`,
  `MMP.Fourfold.natCast_finrank_cotangentSpace_sub_le`: the bound for a Noetherian local
  `k`-algebra with residue field `k`.
* `MMP.Fourfold.natCast_finrank_cotangentSpace_sub_le_topologicalKrullDimAt`: the bound for the
  local dimension of a scheme locally of finite type over `k` at a `k`-point.

## Implementation notes

The cotangent space `𝔪/𝔪²` has the same dimension as the tangent space `T_x M`. The local
dimension of `M` at the closed point `x` is `topologicalKrullDimAt M x`, which equals the Krull
dimension of `𝒪_{M,x}`. The hypotheses that `k` is algebraically closed and that `M` is
quasi-compact are not used. Functoriality of the data in the quotient maps (identities and
composition) is not required, and no intermediate lift is chosen.

## References

* Kollár, *Rational curves on algebraic varieties*, I.2.
-/

@[expose] public noncomputable section

open IsLocalRing TensorProduct

universe u v w

namespace MMP.Fourfold

section TensorLemma

variable {k : Type*} [Field k] {V K : Type*} [AddCommGroup V] [Module k V] [AddCommGroup K]
  [Module k K]

/-- For `V` finite dimensional, every `ω ∈ V ⊗ K` admits a family `w` of `dim V` elements of `K`
such that `(1 ⊗ f) ω = 0` for every linear map `f : K → K'` vanishing on all the `w i`. -/
theorem exists_family_lTensor_eq_zero [Module.Finite k V] (ω : V ⊗[k] K) :
    ∃ w : Fin (Module.finrank k V) → K, ∀ {K' : Type*} [AddCommGroup K'] [Module k K']
      (f : K →ₗ[k] K'), (∀ i, f (w i) = 0) → LinearMap.lTensor V f ω = 0 := by
  let b := Module.finBasis k V
  have key : ∃ w : Fin (Module.finrank k V) → K, ω = ∑ i, b i ⊗ₜ[k] w i := by
    induction ω using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul v x =>
      refine ⟨fun i => b.repr v i • x, ?_⟩
      conv_lhs => rw [← b.sum_repr v]
      rw [TensorProduct.sum_tmul]
      simp [TensorProduct.smul_tmul']
    | add y z hy hz =>
      obtain ⟨w, rfl⟩ := hy
      obtain ⟨w', rfl⟩ := hz
      exact ⟨w + w', by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  obtain ⟨w, rfl⟩ := key
  refine ⟨w, fun f hf => ?_⟩
  simp [hf]

end TensorLemma

/-! ### Local Artinian algebras and small extensions -/

/-- A local Artinian `k`-algebra with residue field `k`: an object of the category of "local
Artinian lifting problems at a `k`-point". -/
structure ArtinLocalAlgebra (k : Type u) [Field k] where
  /-- The underlying ring. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra k carrier]
  [isLocalRing : IsLocalRing carrier]
  [isArtinianRing : IsArtinianRing carrier]
  /-- The residue field of the ring is `k`. -/
  residue_bijective : Function.Bijective (algebraMap k (ResidueField carrier))

attribute [instance] ArtinLocalAlgebra.commRing ArtinLocalAlgebra.algebra
  ArtinLocalAlgebra.isLocalRing ArtinLocalAlgebra.isArtinianRing

variable {k : Type u} [Field k]

/-- A small extension of the local Artinian `k`-algebra `A`: a surjection `π : B → A` of local
Artinian `k`-algebras with residue field `k` whose kernel `J` is killed by the maximal ideal. -/
structure SmallExtension (A : ArtinLocalAlgebra k) where
  /-- The extension `B`. -/
  big : ArtinLocalAlgebra k
  /-- The surjection `B → A`. -/
  π : big.carrier →ₐ[k] A.carrier
  /-- The map `B → A` is surjective. -/
  surjective : Function.Surjective π
  /-- The kernel is killed by the maximal ideal of `B`. -/
  ker_mul_maximalIdeal : RingHom.ker π * maximalIdeal big.carrier = ⊥

namespace SmallExtension

variable {A : ArtinLocalAlgebra k} (E : SmallExtension A)

/-- The kernel `J` of a small extension, as a `k`-vector space. -/
def kernel : Submodule k E.big.carrier := LinearMap.ker E.π.toLinearMap

/-- An element lies in the kernel of a small extension iff its image in `A` is zero. -/
@[simp]
theorem mem_kernel {x : E.big.carrier} : x ∈ E.kernel ↔ E.π x = 0 := Iff.rfl

/-- A quotient map of small extensions of `A`: a surjection `B → B'` of the extending algebras
compatible with the maps to `A`; it is the quotient of `B` by a subspace of the kernel. -/
structure QuotientMap (E E' : SmallExtension A) where
  /-- The surjection `B → B'`. -/
  toAlgHom : E.big.carrier →ₐ[k] E'.big.carrier
  /-- The map `B → B'` is surjective. -/
  surjective : Function.Surjective toAlgHom
  /-- The map `B → B'` is compatible with the maps to `A`. -/
  comp_π : E'.π.comp toAlgHom = E.π

variable {E} {E' : SmallExtension A}

/-- The induced `k`-linear map between the kernels of two small extensions. -/
def QuotientMap.kerMap (q : QuotientMap E E') : E.kernel →ₗ[k] E'.kernel :=
  q.toAlgHom.toLinearMap.restrict fun x hx => by
    change E'.π (q.toAlgHom x) = 0
    rw [← AlgHom.comp_apply, q.comp_π]
    exact hx

@[simp]
theorem QuotientMap.coe_kerMap_apply (q : QuotientMap E E') (x : E.kernel) :
    (q.kerMap x : E'.big.carrier) = q.toAlgHom x := rfl

end SmallExtension

/-- **Two-stage obstruction theory** at a `k`-point, for the local ring `R` of a scheme at the
point. The points of the scheme over a local Artinian `k`-algebra `A`, lying over the given
`k`-point, are the `k`-algebra homomorphisms `R → A`; a lifting problem is a small extension
`B → A` together with such a point `a`. A two-stage obstruction theory with obstruction spaces
`V₁`, `V₂` consists of

* a first obstruction `obs₁ E a ∈ V₁ ⊗ J`, `J` the kernel of `E`;
* a type `Intermediate E a` of intermediate lifts, nonempty when the first obstruction vanishes,
  each with a second obstruction `obs₂ ∈ V₂ ⊗ J`;
* the vanishing of the second obstruction of an intermediate lift gives a lift `b : R → B` of `a`;
* compatibility with quotienting `J`: an intermediate lift is carried to the quotient extension
  `B/J' → A` (a `QuotientMap`, that is the quotient by a subspace `J' ≤ J`), and the obstructions
  are carried to those of the quotient extension by the induced maps on kernels.

No intermediate lift is *chosen* coherently for all quotient maps: such a choice cannot exist for
real moduli problems, since automorphisms of `B` over `A` (e.g. `t ↦ t + c t²` on
`k[t]/t³ → k[t]/t²`) move intermediate lifts by nonzero derivations. -/
structure TwoStageObstructionTheory (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R]
    (V₁ V₂ : Type v) [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] where
  /-- The intermediate lifts of a point `a` along a small extension. -/
  Intermediate : ∀ {A : ArtinLocalAlgebra k}, SmallExtension A → (R →ₐ[k] A.carrier) → Type w
  /-- The first obstruction, in `V₁ ⊗ J`. -/
  obs₁ : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier),
    V₁ ⊗[k] E.kernel
  /-- The second obstruction of an intermediate lift, in `V₂ ⊗ J`. -/
  obs₂ : ∀ {A : ArtinLocalAlgebra k} {E : SmallExtension A} {a : R →ₐ[k] A.carrier},
    Intermediate E a → V₂ ⊗[k] E.kernel
  /-- When the first obstruction vanishes an intermediate lift exists. -/
  exists_intermediate : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A)
    (a : R →ₐ[k] A.carrier), obs₁ E a = 0 → Nonempty (Intermediate E a)
  /-- The vanishing of the second obstruction of an intermediate lift gives a lift of the point. -/
  exists_lift : ∀ {A : ArtinLocalAlgebra k} (E : SmallExtension A) (a : R →ₐ[k] A.carrier)
    (m : Intermediate E a), obs₂ m = 0 → ∃ b : R →ₐ[k] E.big.carrier, E.π.comp b = a
  /-- Intermediate lifts are carried to the quotient extension. -/
  mapIntermediate : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A}
    (q : E.QuotientMap E') {a : R →ₐ[k] A.carrier}, Intermediate E a → Intermediate E' a
  /-- The first obstruction is carried to that of the quotient extension by the induced map on
  kernels. -/
  obs₁_map : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    (a : R →ₐ[k] A.carrier), obs₁ E' a = LinearMap.lTensor V₁ q.kerMap (obs₁ E a)
  /-- The second obstruction of an intermediate lift is carried to that of its image by the
  induced map on kernels. -/
  obs₂_map : ∀ {A : ArtinLocalAlgebra k} {E E' : SmallExtension A} (q : E.QuotientMap E')
    {a : R →ₐ[k] A.carrier} (m : Intermediate E a),
    obs₂ (mapIntermediate q m) = LinearMap.lTensor V₂ q.kerMap (obs₂ m)

section Generic

/-- Surjections of local `k`-algebras preserve "residue field `k`". -/
theorem residue_bijective_of_surjective {A B : Type*} [CommRing A] [Algebra k A] [IsLocalRing A]
    [CommRing B] [Algebra k B] [IsLocalRing B]
    (hA : Function.Bijective (algebraMap k (ResidueField A))) (f : A →ₐ[k] B)
    (hf : Function.Surjective f) : Function.Bijective (algebraMap k (ResidueField B)) := by
  refine ⟨(algebraMap k (ResidueField B)).injective, fun y => ?_⟩
  have : IsLocalHom f.toRingHom := IsLocalHom.of_surjective f.toRingHom hf
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, rfl⟩ := hf b
  obtain ⟨c, hc⟩ := hA.2 (IsLocalRing.residue A a)
  refine ⟨c, ?_⟩
  have h1 : a - algebraMap k A c ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc]
    exact sub_eq_zero.2 rfl
  have h2 : f (a - algebraMap k A c) ∈ maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun hu => h1 (IsUnit.of_map f.toRingHom _ hu)
  have h3 : IsLocalRing.residue B (f a) = IsLocalRing.residue B (f (algebraMap k A c)) := by
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).2 h2
  rw [h3, AlgHom.commutes]
  rfl

/-- If the maximal ideal `𝔪` of a local ring `P` is carried by `φ₁` into the maximal ideal of
`B`, and `φ₂` is another ring map `P → B` agreeing with `φ₁` modulo a kernel `ker π` killed by
the maximal ideal of `B`, then `φ₁` and `φ₂` agree on `𝔪²`. -/
theorem eq_of_mem_mul {P B A : Type*} [CommRing P] [CommRing B] [CommRing A] [IsLocalRing B]
    (mP : Ideal P) (φ₁ φ₂ : P →+* B) (π : B →+* A) (hπ : ∀ x, π (φ₁ x) = π (φ₂ x))
    (hker : RingHom.ker π ≤ maximalIdeal B) (hker2 : RingHom.ker π * maximalIdeal B = ⊥)
    (hφ : ∀ x ∈ mP, φ₁ x ∈ maximalIdeal B) : ∀ f ∈ mP * mP, φ₁ f = φ₂ f := by
  intro f hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun x y hx hy => by
    rw [map_add, map_add, hx, hy])
  have hka : φ₂ a - φ₁ a ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_sub, hπ, sub_self]
  have hkb : φ₂ b - φ₁ b ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_sub, hπ, sub_self]
  have h0 : ∀ {u v : B}, u ∈ RingHom.ker π → v ∈ maximalIdeal B → u * v = 0 := fun hu hv => by
    simpa [hker2] using Ideal.mul_mem_mul hu hv
  rw [map_mul, map_mul]
  linear_combination -h0 hka (hφ b hb) - h0 hkb (hφ a ha) - h0 hka (hker hkb)

/-- A local Artinian `k`-algebra with residue field `k`, presented as a quotient of a Noetherian
local `k`-algebra `A` (with residue field `k`) by an ideal containing a power of its maximal
ideal. -/
def ArtinLocalAlgebra.ofSurjective {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : Function.Bijective (algebraMap k (ResidueField A))) {B : Type u}
    [CommRing B] [Algebra k B] [Nontrivial B] (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (s : ℕ) (hs : maximalIdeal A ^ s ≤ RingHom.ker f) : ArtinLocalAlgebra k :=
  letI : IsLocalRing B := IsLocalRing.of_surjective' f.toRingHom hf
  haveI : IsNoetherianRing B := isNoetherianRing_of_surjective A B f.toRingHom hf
  { carrier := B
    residue_bijective := residue_bijective_of_surjective hA f hf
    isArtinianRing := by
      refine (isArtinianRing_iff_isNilpotent_maximalIdeal B).2 ⟨s, ?_⟩
      have : IsLocalHom f.toRingHom := IsLocalHom.of_surjective f.toRingHom hf
      rw [← IsLocalRing.map_maximalIdeal_of_surjective f.toRingHom hf, ← Ideal.map_pow]
      refine le_antisymm ((Ideal.map_mono hs).trans ?_) bot_le
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simpa [RingHom.mem_ker] using hx }

/-- A local homomorphism into a local ring whose maximal ideal has vanishing `N`-th power kills
the `N`-th power of the maximal ideal. -/
theorem maximalIdeal_pow_le_ker {R B : Type*} [CommRing R] [IsLocalRing R] [CommRing B]
    [IsLocalRing B] (b : R →+* B) [IsLocalHom b] {N : ℕ} (hB : maximalIdeal B ^ N = ⊥) :
    maximalIdeal R ^ N ≤ RingHom.ker b := by
  intro r hr
  have h := Ideal.mem_map_of_mem b hr
  rw [Ideal.map_pow] at h
  have hle : Ideal.map b (maximalIdeal R) ≤ maximalIdeal B :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit b x hx
  have h' := Ideal.pow_right_mono hle N h
  rw [hB] at h'
  exact RingHom.mem_ker.2 (Ideal.mem_bot.1 h')

/-- **Artin–Rees** for an ideal `I` of a Noetherian ring: `m ^ (κ + 1) ⊓ I ≤ m * I` for some
`κ`. -/
theorem exists_pow_succ_inf_le_mul {P : Type*} [CommRing P] [IsNoetherianRing P]
    (m I : Ideal P) : ∃ κ, m ^ (κ + 1) ⊓ I ≤ m * I := by
  obtain ⟨κ, hκ⟩ := Ideal.exists_pow_inf_eq_pow_smul m (I : Submodule P P)
  refine ⟨κ, ?_⟩
  have h := hκ (κ + 1) (Nat.le_succ κ)
  have h1 : m ^ (κ + 1) • (⊤ : Submodule P P) = m ^ (κ + 1) := by
    rw [smul_eq_mul, Ideal.mul_top]
  rw [Nat.add_sub_cancel_left, pow_one, h1] at h
  rw [h]
  exact (Submodule.smul_mono le_rfl inf_le_right).trans (by rw [smul_eq_mul])

/-- **A Nakayama bound.** Let `I`, `K` be ideals of a Noetherian local ring with `K ≤ I + 𝔪ᴺ` and
`𝔪ᴺ ⊓ I ≤ 𝔪 I`. If `I` lies in `𝔪 K + 𝔪ᴺ` plus the span of `m₁ + m₂` elements of `K`, then `I`
is generated by `m₁ + m₂` elements. -/
theorem spanFinrank_le_of_le_sup_span {P : Type*} [CommRing P] [IsLocalRing P]
    [IsNoetherianRing P] {I K : Ideal P} {N m₁ m₂ : ℕ} (hK : K ≤ I ⊔ maximalIdeal P ^ N)
    (hAR : maximalIdeal P ^ N ⊓ I ≤ maximalIdeal P * I) (p₁ : Fin m₁ → P) (p₂ : Fin m₂ → P)
    (hp₁ : ∀ i, p₁ i ∈ K) (hp₂ : ∀ i, p₂ i ∈ K)
    (hI : I ≤ maximalIdeal P * K ⊔ maximalIdeal P ^ N ⊔ Ideal.span (Set.range p₁) ⊔
      Ideal.span (Set.range p₂)) :
    I.spanFinrank ≤ m₁ + m₂ := by
  classical
  set mP := maximalIdeal P
  choose g₁ hg₁ e₁ he₁ hge₁ using fun i => Submodule.mem_sup.1 (hK (hp₁ i))
  choose g₂ hg₂ e₂ he₂ hge₂ using fun i => Submodule.mem_sup.1 (hK (hp₂ i))
  let G : Fin m₁ ⊕ Fin m₂ → P := Sum.elim g₁ g₂
  set I' := Ideal.span (Set.range G)
  have hI'I : I' ≤ I := Ideal.span_le.2 (by
    rintro _ ⟨i | i, rfl⟩
    exacts [hg₁ i, hg₂ i])
  have hmK : mP * K ≤ mP * I ⊔ mP ^ N := by
    calc mP * K ≤ mP * (I ⊔ mP ^ N) := Ideal.mul_mono_right hK
      _ = mP * I ⊔ mP * mP ^ N := Ideal.mul_sup _ _ _
      _ ≤ mP * I ⊔ mP ^ N := sup_le_sup_left Ideal.mul_le_right _
  have hJ₃le : mP * K ⊔ mP ^ N ⊔ Ideal.span (Set.range p₁) ⊔ Ideal.span (Set.range p₂) ≤
      I' ⊔ (mP * I ⊔ mP ^ N) := by
    refine sup_le (sup_le (sup_le (hmK.trans le_sup_right) ?_) ?_) ?_
    · exact (le_sup_right : mP ^ N ≤ mP * I ⊔ mP ^ N).trans le_sup_right
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      rw [← hge₁ i]
      exact add_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨Sum.inl i, rfl⟩))
        (Ideal.mem_sup_right (Ideal.mem_sup_right (he₁ i)))
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      rw [← hge₂ i]
      exact add_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨Sum.inr i, rfl⟩))
        (Ideal.mem_sup_right (Ideal.mem_sup_right (he₂ i)))
  have hNN : I ≤ I' ⊔ mP • I := by
    intro f hf
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hJ₃le (hI hf))
    have hz' : z ∈ (mP * I ⊔ mP ^ N) ⊓ I := ⟨hz, (I.add_mem_iff_right (hI'I hy)).1 hf⟩
    rw [sup_inf_assoc_of_le _ (Ideal.mul_le_right : mP * I ≤ I)] at hz'
    have hz'' : z ∈ mP * I := (sup_le le_rfl hAR) hz'
    exact Submodule.mem_sup.2 ⟨y, hy, z, by rwa [smul_eq_mul], rfl⟩
  have hIle : I ≤ I' := Submodule.le_of_le_smul_of_le_jacobson_bot (I := mP) (N := I') (N' := I)
    (IsNoetherian.noetherian I)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm.le hNN
  calc I.spanFinrank = I'.spanFinrank := by rw [le_antisymm hIle hI'I]
    _ ≤ (Set.range G).ncard := Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range G)
    _ = (G '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set (Fin m₁ ⊕ Fin m₂)).ncard := Set.ncard_image_le Set.finite_univ
    _ = m₁ + m₂ := by
        rw [Set.ncard_univ]
        simp

end Generic

section Truncation

variable {P : Type u} [CommRing P] [Algebra k P] [IsLocalRing P] [IsNoetherianRing P]

omit [IsNoetherianRing P] in
/-- If `η : P → A` kills `J` and `𝔪 · ker η ≤ J`, then the kernel of the induced map
`P/J → A` is killed by the maximal ideal of `P/J`. -/
theorem ker_liftₐ_mul_maximalIdeal {A : Type*} [CommRing A] [Algebra k A] (η : P →ₐ[k] A)
    (J : Ideal P) (hJ : ∀ x ∈ J, η x = 0) (hJm : maximalIdeal P * RingHom.ker η ≤ J)
    [IsLocalRing (P ⧸ J)] :
    RingHom.ker (Ideal.Quotient.liftₐ J η hJ) * maximalIdeal (P ⧸ J) = ⊥ := by
  refine le_antisymm (Ideal.mul_le.2 fun u hu v hv => ?_) bot_le
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hv' : v ∈ Ideal.map (Ideal.Quotient.mk J) (maximalIdeal P) := by
    rwa [IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective]
  obtain ⟨q, hq, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
    Ideal.Quotient.mk_surjective).1 hv'
  have hp : p ∈ RingHom.ker η := RingHom.mem_ker.1 hu
  rw [← map_mul, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, mul_comm]
  exact hJm (Ideal.mul_mem_mul hq hp)

/-- The small extension `P/J → A` obtained from a surjection `η : P → A` onto a local Artinian
`k`-algebra with residue field `k`, and an ideal `J ≤ ker η` with `𝔪 · ker η ≤ J` and
`𝔪ˢ ≤ J`. -/
def truncExtension (hP : Function.Bijective (algebraMap k (ResidueField P)))
    (A : ArtinLocalAlgebra k) (η : P →ₐ[k] A.carrier) (hη : Function.Surjective η)
    (J : Ideal P) (hJ : J ≤ RingHom.ker η) (hJm : maximalIdeal P * RingHom.ker η ≤ J) (s : ℕ)
    (hs : maximalIdeal P ^ s ≤ J) : SmallExtension A := by
  haveI : Nontrivial (P ⧸ J) := Ideal.Quotient.nontrivial_iff.2 (fun h => by
    have := hJ (h ▸ Submodule.mem_top : (1 : P) ∈ J)
    exact one_ne_zero ((map_one η).symm.trans (RingHom.mem_ker.1 this)))
  letI : IsLocalRing (P ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  exact
  { big := ArtinLocalAlgebra.ofSurjective hP (Ideal.Quotient.mkₐ k J)
      (Ideal.Quotient.mkₐ_surjective k J) s (fun x hx => by
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hs hx)
    π := Ideal.Quotient.liftₐ J η (fun x hx => RingHom.mem_ker.1 (hJ hx))
    surjective := by
      intro y
      obtain ⟨p, rfl⟩ := hη y
      exact ⟨Ideal.Quotient.mk J p, rfl⟩
    ker_mul_maximalIdeal :=
      ker_liftₐ_mul_maximalIdeal η J (fun x hx => RingHom.mem_ker.1 (hJ hx)) hJm }

/-- Data for a family of small extensions of `A` by quotients of `P`: a surjection `η : P → A`
onto a local Artinian `k`-algebra with residue field `k`, and an exponent `s` such that the
truncating ideals are required to contain `𝔪ˢ`. -/
structure TruncData (k : Type u) [Field k] (P : Type u) [CommRing P] [Algebra k P]
    [IsLocalRing P] where
  /-- The residue field of `P` is `k`. -/
  residue_bijective : Function.Bijective (algebraMap k (ResidueField P))
  /-- The target local Artinian `k`-algebra. -/
  A : ArtinLocalAlgebra k
  /-- The surjection `P → A`. -/
  η : P →ₐ[k] A.carrier
  /-- The map `η` is surjective. -/
  surjective : Function.Surjective η
  /-- The exponent `s` such that the truncating ideals contain `𝔪ˢ`. -/
  s : ℕ

namespace TruncData

variable (D : TruncData k P)

/-- An ideal `J` with `𝔪 · ker η ≤ J ≤ ker η` and `𝔪ˢ ≤ J`. -/
def Adm (J : Ideal P) : Prop :=
  J ≤ RingHom.ker D.η ∧ maximalIdeal P * RingHom.ker D.η ≤ J ∧ maximalIdeal P ^ D.s ≤ J

/-- The small extension `P/J → A`. -/
def extension (J : Ideal P) (h : D.Adm J) : SmallExtension D.A :=
  truncExtension D.residue_bijective D.A D.η D.surjective J h.1 h.2.1 D.s h.2.2

/-- The map `P/J → A` of `D.extension J h` sends the class of `p` to `η p`. -/
theorem extension_π_mk {J : Ideal P} (h : D.Adm J) (p : P) :
    (D.extension J h).π (Ideal.Quotient.mk J p) = D.η p := rfl

/-- The quotient map `P/J → P/J'` for `J ≤ J'`. -/
def quotientMap {J J' : Ideal P} (h : D.Adm J) (h' : D.Adm J') (hle : J ≤ J') :
    (D.extension J h).QuotientMap (D.extension J' h') where
  toAlgHom := Ideal.Quotient.factorₐ k hle
  surjective := Ideal.Quotient.factor_surjective hle
  comp_π := by
    refine AlgHom.ext fun x => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- **One stage of the quotient argument.** Given `ω ∈ V ⊗ K`, `K` the kernel of the
extension `P/J → A`, adding to `J` at most `dim V` elements `p i` of `ker η` gives an
admissible `J' ≥ J` whose quotient extension kills the image of `ω`. -/
theorem exists_stage {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {J : Ideal P} (hJ : D.Adm J) (ω : V ⊗[k] (D.extension J hJ).kernel) :
    ∃ (p : Fin (Module.finrank k V) → P) (hJ' : D.Adm (J ⊔ Ideal.span (Set.range p))),
      (∀ i, p i ∈ RingHom.ker D.η) ∧
      LinearMap.lTensor V (D.quotientMap hJ hJ' le_sup_left).kerMap ω = 0 := by
  obtain ⟨w, hw⟩ := exists_family_lTensor_eq_zero (k := k) ω
  choose p hp using fun i => Ideal.Quotient.mk_surjective (w i).1
  have hpk : ∀ i, p i ∈ RingHom.ker D.η := fun i => by
    rw [RingHom.mem_ker, ← D.extension_π_mk hJ, hp i]
    exact (w i).2
  have hadm : D.Adm (J ⊔ Ideal.span (Set.range p)) := by
    refine ⟨sup_le hJ.1 (Ideal.span_le.2 ?_), hJ.2.1.trans le_sup_left,
      hJ.2.2.trans le_sup_left⟩
    rintro _ ⟨i, rfl⟩
    exact hpk i
  refine ⟨p, hadm, hpk, hw _ fun i => ?_⟩
  refine Subtype.ext ?_
  change (Ideal.Quotient.factorₐ k (le_sup_left : J ≤ J ⊔ Ideal.span (Set.range p))) (w i).1 = 0
  rw [← hp i]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))

/-- **The two-stage lifting.** Starting from an admissible `J₁`, adding at most `dim V₁` elements
of `ker η` and then at most `dim V₂` elements of `ker η` gives an admissible `J₃` such that the
point `a : R → A` lifts to `P/J₃` (by the first obstruction killed, then the second). -/
theorem exists_two_stage_lift {R : Type u} [CommRing R] [Algebra k R]
    {V₁ V₂ : Type v} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    [Module.Finite k V₁] [Module.Finite k V₂] (T : TwoStageObstructionTheory.{u, v, w} k R V₁ V₂)
    (a : R →ₐ[k] D.A.carrier) {J₁ : Ideal P} (h₁ : D.Adm J₁) :
    ∃ (p₁ : Fin (Module.finrank k V₁) → P) (p₂ : Fin (Module.finrank k V₂) → P)
      (hJ : D.Adm (J₁ ⊔ Ideal.span (Set.range p₁) ⊔ Ideal.span (Set.range p₂))),
      (∀ i, p₁ i ∈ RingHom.ker D.η) ∧ (∀ i, p₂ i ∈ RingHom.ker D.η) ∧
        ∃ b : R →ₐ[k] (D.extension _ hJ).big.carrier, (D.extension _ hJ).π.comp b = a := by
  obtain ⟨p₁, hJ₂, hp₁, hv₁⟩ := D.exists_stage h₁ (T.obs₁ (D.extension J₁ h₁) a)
  obtain ⟨m⟩ := T.exists_intermediate (D.extension _ hJ₂) a
    ((T.obs₁_map (D.quotientMap h₁ hJ₂ le_sup_left) a).trans hv₁)
  obtain ⟨p₂, hJ₃, hp₂, hv₂⟩ := D.exists_stage hJ₂ (T.obs₂ m)
  exact ⟨p₁, p₂, hJ₃, hp₁, hp₂, T.exists_lift _ a (T.mapIntermediate
    (D.quotientMap hJ₂ hJ₃ le_sup_left) m)
      ((T.obs₂_map (D.quotientMap hJ₂ hJ₃ le_sup_left) m).trans hv₂)⟩

/-- If the extension `P/J → A` has a section, then `J` contains every element of `𝔪²` killed by
`η`. -/
theorem sq_inf_ker_le_of_section {J : Ideal P} (hJ : D.Adm J)
    (ψ : D.A.carrier →ₐ[k] (D.extension J hJ).big.carrier)
    (hψ : (D.extension J hJ).π.comp ψ = AlgHom.id k D.A.carrier) :
    maximalIdeal P ^ 2 ⊓ RingHom.ker D.η ≤ J := by
  rintro f ⟨hf, hηf⟩
  let E := D.extension J hJ
  let φ₁ : P →+* E.big.carrier := Ideal.Quotient.mk J
  have hmB : maximalIdeal E.big.carrier = Ideal.map φ₁ (maximalIdeal P) :=
    (IsLocalRing.map_maximalIdeal_of_surjective φ₁ Ideal.Quotient.mk_surjective).symm
  have hπ : ∀ x, E.π.toRingHom (φ₁ x) = E.π.toRingHom ((ψ.toRingHom.comp D.η.toRingHom) x) :=
    fun x => (AlgHom.congr_fun hψ (D.η x)).symm
  have h := eq_of_mem_mul (maximalIdeal P) φ₁ (ψ.toRingHom.comp D.η.toRingHom) E.π.toRingHom hπ
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)) E.ker_mul_maximalIdeal
    (fun x hx => hmB ▸ Ideal.mem_map_of_mem _ hx) f (by rwa [← pow_two])
  have h0 : (ψ.toRingHom.comp D.η.toRingHom) f = 0 := by
    change ψ (D.η f) = 0
    rw [RingHom.mem_ker.1 hηf, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.1 (h.trans h0)

end TruncData

end Truncation

section Presentation

variable {R : Type u} [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]

/-- The completion of a Noetherian local `k`-algebra with residue field `k` is a quotient of the
power series ring in `n = dim 𝔪/𝔪²` variables, by an ideal inside the square of the maximal
ideal. -/
theorem exists_presentation (hk : Function.Bijective (algebraMap k (ResidueField R))) :
    ∃ F : MvPowerSeries (Fin (maximalIdeal R).spanFinrank) k →+*
        AdicCompletion (maximalIdeal R) R,
      Function.Surjective F ∧
        (∀ c, F (MvPowerSeries.C c) = algebraMap R _ (algebraMap k R c)) ∧
        RingHom.ker F ≤
          maximalIdeal (MvPowerSeries (Fin (maximalIdeal R).spanFinrank) k) ^ 2 := by
  set n := (maximalIdeal R).spanFinrank with hn
  obtain ⟨x, hx⟩ := Stacks.CompleteLocalRing.PowerSeriesRing.exists_fin_generating_family
    (maximalIdeal R).fg_of_isNoetherianRing hn
  have hspan : Ideal.span (Set.range fun i => algebraMap R (AdicCompletion (maximalIdeal R) R)
      (x i)) = maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
    refine Eq.trans ?_ AdicCompletion.maximalIdeal_eq_map.symm
    have : Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R) =
        Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R))
          (Ideal.span (Set.range x)) := congrArg _ hx.symm
    refine Eq.trans ?_ this.symm
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hf : Function.Surjective ((Ideal.Quotient.mk
      (maximalIdeal (AdicCompletion (maximalIdeal R) R))).comp
      ((algebraMap R (AdicCompletion (maximalIdeal R) R)).comp (algebraMap k R))) := by
    intro y
    obtain ⟨z, hz⟩ := (AdicCompletion.residueField_map_bijective R).2 y
    obtain ⟨c, hc⟩ := hk.2 z
    refine ⟨c, ?_⟩
    rw [← hz, ← hc]
    exact (IsLocalRing.ResidueField.map_residue (algebraMap R _) (algebraMap k R c)).symm
  obtain ⟨F, hFs, -, hFC⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom
      (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (fun i => algebraMap R (AdicCompletion (maximalIdeal R) R) (x i)) hspan
      ((algebraMap R (AdicCompletion (maximalIdeal R) R)).comp (algebraMap k R)) hf
  refine ⟨F, hFs, hFC, ?_⟩
  refine Stacks.RegularLocalRing.SpanFinrank.ker_le_maximalIdeal_sq_of_surjective_of_spanFinrank_eq
    F hFs ?_
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq,
    IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    Stacks.MvPowerSeries.RegularParameters.finrank_cotangentSpace_field]

omit [Algebra k R] in
/-- **Krull's height theorem for a presentation**: `dim k[[z₁,…,zₙ]] = n ≤ dim R + μ(I)`, where
`μ(I)` is the minimal number of generators of the kernel `I` of `k[[z₁,…,zₙ]] ↠ R̂`. -/
theorem natCast_le_ringKrullDim_add_spanFinrank_ker {n : ℕ}
    (F : MvPowerSeries (Fin n) k →+* AdicCompletion (maximalIdeal R) R)
    (hFs : Function.Surjective F) :
    (n : WithBot ℕ∞) ≤ ringKrullDim R + (RingHom.ker F).spanFinrank := by
  have hI : RingHom.ker F ≤ Ring.jacobson (MvPowerSeries (Fin n) k) := by
    rw [Ring.jacobson_eq_sInf_isMaximal]
    refine le_sInf fun m hm => ?_
    have : RingHom.ker F ≤ maximalIdeal (MvPowerSeries (Fin n) k) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top F)
    exact this.trans (IsLocalRing.eq_maximalIdeal hm ▸ le_rfl)
  have h := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (RingHom.ker F) hI
  rwa [MvPowerSeries.ringKrullDim_eq, ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective hFs),
    ← ringKrullDim_adicCompletion_maximalIdeal (A := R)] at h

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- The kernel of the evaluation map `R̂ → R/𝔪ⁿ` is generated by `𝔪ⁿ`. -/
theorem ker_evalₐ_eq_map {I : Ideal R} (hI : I.FG) (N : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I N : AdicCompletion I R →ₐ[R] R ⧸ I ^ N) =
      Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ N) := by
  ext x
  have h := AdicCompletion.pow_smul_top_eq_ker_eval (M := R) (n := N) hI
  have h2 : x ∈ (I ^ N • (⊤ : Submodule R (AdicCompletion I R))) ↔
      x ∈ Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ N) := by
    rw [Ideal.smul_top_eq_map]
    rfl
  rw [← h2, h]
  have hsm : I ^ N • (⊤ : Submodule R R) = I ^ N := by
    rw [smul_eq_mul, Ideal.mul_top]
  have hfac := AdicCompletion.factor_eval_eq_evalₐ (I := I) x hsm.le
  rw [RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I R N x)
    rw [← hy] at hfac ⊢
    have h3 : y ∈ I ^ N := Ideal.Quotient.eq_zero_iff_mem.1 <| by
      rw [← hx, ← hfac]
      rfl
    exact Submodule.Quotient.mk_eq_zero _ |>.2 (by rwa [hsm])
  · intro hx
    rw [← hfac, hx]
    simp

/-- The truncation of a presentation: the surjection `k[[z]] → R̂ → R/𝔪ᴺ` has kernel
`I + 𝔪ᴺ`, where `I` is the kernel of `k[[z]] ↠ R̂`. -/
theorem exists_truncation {n : ℕ}
    (F : MvPowerSeries (Fin n) k →+* AdicCompletion (maximalIdeal R) R)
    (hFs : Function.Surjective F)
    (hFC : ∀ c, F (MvPowerSeries.C c) = algebraMap R _ (algebraMap k R c)) (N : ℕ) :
    ∃ η : MvPowerSeries (Fin n) k →ₐ[k] R ⧸ maximalIdeal R ^ N,
      Function.Surjective η ∧ (∀ f ∈ RingHom.ker F, η f = 0) ∧
        maximalIdeal (MvPowerSeries (Fin n) k) ^ N ≤ RingHom.ker η ∧
        RingHom.ker η ≤ RingHom.ker F ⊔ maximalIdeal (MvPowerSeries (Fin n) k) ^ N := by
  set ev : AdicCompletion (maximalIdeal R) R →+* R ⧸ maximalIdeal R ^ N :=
    (AdicCompletion.evalₐ (maximalIdeal R) N).toRingHom
  have hevι : ∀ r, ev (algebraMap R _ r) = Ideal.Quotient.mk _ r := fun r =>
    AdicCompletion.evalₐ_of (maximalIdeal R) N r
  let η : MvPowerSeries (Fin n) k →ₐ[k] R ⧸ maximalIdeal R ^ N :=
    { ev.comp F with
      commutes' := fun c => by
        change ev (F (MvPowerSeries.C c)) = _
        rw [hFC, hevι]
        rfl }
  have h := ker_evalₐ_eq_map (maximalIdeal R).fg_of_isNoetherianRing N
  rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map] at h
  have hev0 : ∀ s, ev s = 0 ↔ s ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ N := by
    intro s
    rw [← h]
    exact RingHom.mem_ker.symm
  have hmapF : (maximalIdeal (MvPowerSeries (Fin n) k)).map F =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) :=
    IsLocalRing.map_maximalIdeal_of_surjective F hFs
  refine ⟨η, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨p, hp⟩ := hFs (algebraMap R _ r)
    refine ⟨p, ?_⟩
    change ev (F p) = _
    rw [hp, hevι]
  · intro f hf
    change ev (F f) = 0
    rw [RingHom.mem_ker.1 hf, map_zero]
  · intro x hx
    rw [RingHom.mem_ker]
    change ev (F x) = 0
    rw [hev0]
    have : F x ∈ Ideal.map F (maximalIdeal (MvPowerSeries (Fin n) k) ^ N) :=
      Ideal.mem_map_of_mem F hx
    rwa [Ideal.map_pow, hmapF] at this
  · intro x hx
    rw [RingHom.mem_ker] at hx
    change ev (F x) = 0 at hx
    rw [hev0, ← hmapF, ← Ideal.map_pow] at hx
    obtain ⟨g, hg, hgx⟩ := (Ideal.mem_map_iff_of_surjective F hFs).1 hx
    refine Submodule.mem_sup.2 ⟨x - g, RingHom.mem_ker.2 (by rw [map_sub, hgx, sub_self]), g, hg,
      by ring⟩

/-- The residue field of `k[[z₁,…,zₙ]]` is `k`. -/
theorem residue_bijective_mvPowerSeries (n : ℕ) :
    Function.Bijective (algebraMap k (ResidueField (MvPowerSeries (Fin n) k))) := by
  refine ⟨(algebraMap k _).injective, fun y => ?_⟩
  obtain ⟨p, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨MvPowerSeries.constantCoeff p, ?_⟩
  rw [Stacks.MvPowerSeries.RegularParameters.residue_eq_residue_C_constantCoeff]
  rfl

end Presentation

section Core

variable {R : Type u} [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  {V₁ V₂ : Type v} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [Module.Finite k V₁] [Module.Finite k V₂]

/-- **The kernel of the minimal presentation needs at most `dim V₁ + dim V₂` generators.**
If `F : k[[z₁,…,zₙ]] ↠ R̂` is a `k`-compatible surjection with kernel inside `𝔪²`, then a
two-stage obstruction theory with spaces `V₁`, `V₂` forces `ker F` to be generated by at most
`dim V₁ + dim V₂` elements. -/
theorem spanFinrank_ker_le (hk : Function.Bijective (algebraMap k (ResidueField R)))
    (T : TwoStageObstructionTheory.{u, v, w} k R V₁ V₂) {n : ℕ}
    (F : MvPowerSeries (Fin n) k →+* AdicCompletion (maximalIdeal R) R)
    (hFs : Function.Surjective F)
    (hFC : ∀ c, F (MvPowerSeries.C c) = algebraMap R _ (algebraMap k R c))
    (hsq : RingHom.ker F ≤ maximalIdeal (MvPowerSeries (Fin n) k) ^ 2) :
    (RingHom.ker F).spanFinrank ≤ Module.finrank k V₁ + Module.finrank k V₂ := by
  set P := MvPowerSeries (Fin n) k
  set mP := maximalIdeal P
  obtain ⟨κ, hAR⟩ := exists_pow_succ_inf_le_mul mP (RingHom.ker F)
  set N := κ + 1
  obtain ⟨η, hηs, hηF, hK1, hK2⟩ := exists_truncation F hFs hFC N
  have hNpos : maximalIdeal R ^ N ≠ ⊤ := fun h => by
    have : maximalIdeal R ^ N ≤ maximalIdeal R := Ideal.pow_le_self (by omega)
    exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ this))
  have : Nontrivial (R ⧸ maximalIdeal R ^ N) := Ideal.Quotient.nontrivial_iff.2 hNpos
  have : IsLocalRing (R ⧸ maximalIdeal R ^ N) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let A : ArtinLocalAlgebra k := ArtinLocalAlgebra.ofSurjective hk
    (Ideal.Quotient.mkₐ k (maximalIdeal R ^ N)) (Ideal.Quotient.mkₐ_surjective k _) N
    (fun x hx => by simpa [Ideal.Quotient.eq_zero_iff_mem] using hx)
  let D : TruncData k P :=
    { residue_bijective := residue_bijective_mvPowerSeries n
      A := A
      η := η
      surjective := hηs
      s := N }
  have hJ₁ : D.Adm (mP * RingHom.ker η ⊔ mP ^ N) :=
    ⟨sup_le Ideal.mul_le_right hK1, le_sup_left, le_sup_right⟩
  let a : R →ₐ[k] A.carrier := Ideal.Quotient.mkₐ k (maximalIdeal R ^ N)
  obtain ⟨p₁, p₂, hJ, hp₁, hp₂, b, hb⟩ := D.exists_two_stage_lift T a hJ₁
  set J₃ := mP * RingHom.ker η ⊔ mP ^ N ⊔ Ideal.span (Set.range p₁) ⊔ Ideal.span (Set.range p₂)
  let E := D.extension J₃ hJ
  let φ₁ : P →+* E.big.carrier := Ideal.Quotient.mk J₃
  have hmB : maximalIdeal E.big.carrier = Ideal.map φ₁ mP :=
    (IsLocalRing.map_maximalIdeal_of_surjective φ₁ Ideal.Quotient.mk_surjective).symm
  have hbpow : maximalIdeal E.big.carrier ^ N = ⊥ := by
    rw [hmB, ← Ideal.map_pow]
    refine le_antisymm ?_ bot_le
    rw [Ideal.map_le_iff_le_comap]
    exact fun x hx => Ideal.mem_bot.2 (Ideal.Quotient.eq_zero_iff_mem.2 (hJ.2.2 hx))
  have : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R ^ N)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom b.toRingHom := ⟨fun r (hu : IsUnit (b r)) => by
    have h := hu.map E.π
    rw [← AlgHom.comp_apply, hb] at h
    exact (isUnit_map_iff (Ideal.Quotient.mk (maximalIdeal R ^ N)) r).1 h⟩
  refine spanFinrank_le_of_le_sup_span hK2 hAR p₁ p₂ hp₁ hp₂ fun f hf =>
    D.sq_inf_ker_le_of_section hJ (Ideal.Quotient.liftₐ (maximalIdeal R ^ N) b fun r hr =>
      RingHom.mem_ker.1 (maximalIdeal_pow_le_ker b.toRingHom hbpow hr)) ?_
      (Submodule.mem_inf.2 ⟨hsq hf, RingHom.mem_ker.2 (hηF f hf)⟩)
  refine AlgHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact AlgHom.congr_fun hb r

/-- **A local dimension bound from two successive obstruction spaces** (ring-level form). Let
`R` be a Noetherian local `k`-algebra with residue field `k` (for instance the local ring at a
`k`-point of a scheme locally of finite type over `k`). If every local Artinian lifting problem at
the point is solvable in two stages with finite dimensional obstruction spaces `V₁`, `V₂`, then
`dim R + dim V₁ + dim V₂ ≥ dim 𝔪/𝔪²`, that is `dim R ≥ t - dim V₁ - dim V₂`. -/
theorem natCast_finrank_cotangentSpace_le (hk : Function.Bijective (algebraMap k (ResidueField R)))
    (T : TwoStageObstructionTheory.{u, v, w} k R V₁ V₂) :
    (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) ≤
      ringKrullDim R + ((Module.finrank k V₁ + Module.finrank k V₂ : ℕ) : WithBot ℕ∞) := by
  obtain ⟨F, hFs, hFC, hsq⟩ := exists_presentation hk
  have h1 := natCast_le_ringKrullDim_add_spanFinrank_ker F hFs
  have h2 := spanFinrank_ker_le hk T F hFs hFC hsq
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R]
  refine h1.trans ?_
  gcongr

/-- Subtractive form of `natCast_finrank_cotangentSpace_le`:
`dim R ≥ t - dim V₁ - dim V₂` (with truncated subtraction, which is no restriction since
`dim R ≥ 0`). -/
theorem natCast_finrank_cotangentSpace_sub_le
    (hk : Function.Bijective (algebraMap k (ResidueField R)))
    (T : TwoStageObstructionTheory.{u, v, w} k R V₁ V₂) :
    ((Module.finrank (ResidueField R) (CotangentSpace R) -
        (Module.finrank k V₁ + Module.finrank k V₂) : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R := by
  have h := natCast_finrank_cotangentSpace_le hk T
  set t := Module.finrank (ResidueField R) (CotangentSpace R)
  set d := Module.finrank k V₁ + Module.finrank k V₂
  rcases le_or_gt t d with hle | hlt
  · rw [Nat.sub_eq_zero_of_le hle]
    simpa using ringKrullDim_nonneg_of_nontrivial (R := R)
  · have e : ((t - d : ℕ) : WithBot ℕ∞) + (d : WithBot ℕ∞) = t :=
      mod_cast Nat.sub_add_cancel hlt.le
    rw [← e] at h
    exact ENat.WithBot.add_le_add_natCast_right_iff.mp h

end Core

section Scheme

open CategoryTheory AlgebraicGeometry

/-- **A local dimension bound from two successive obstruction spaces.** Let `M` be a scheme locally
of finite type over a field `k` (algebraic closedness and quasi-compactness are not needed),
`x = s p` the image of a point `s : Spec k ⟶ M` of `M(k)` (a section of the structure map `sM`), and
`t = dim_k T_x M` the dimension of the cotangent space `𝔪/𝔪²` of `𝒪_{M,x}` (equal to that of its
dual, the tangent space). Suppose every local Artinian lifting problem at `x` is solved in two
stages with finite dimensional obstruction spaces `V₁`, `V₂`, in the sense of
`TwoStageObstructionTheory` (the `M`-points of `Spec A` over `x` being the `k`-algebra homomorphisms
`𝒪_{M,x} → A`). Then `dim_x M ≥ t - dim V₁ - dim V₂`, where `dim_x M` is the local dimension
`topologicalKrullDimAt M x` (truncated subtraction is harmless as `dim_x M ≥ 0`). -/
@[mmp "lem_fourfold_two_stage_obstruction_dimension"]
theorem natCast_finrank_cotangentSpace_sub_le_topologicalKrullDimAt
    {M : Scheme.{u}} (sM : M ⟶ Spec (.of k)) [LocallyOfFiniteType sM]
    (s : Spec (.of k) ⟶ M) (hs : s ≫ sM = 𝟙 _) (p : Spec (.of k))
    {V₁ V₂ : Type v} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    [Module.Finite k V₁] [Module.Finite k V₂]
    (T : @TwoStageObstructionTheory.{u, v, w} k _ (M.presheaf.stalk (s p)) _
      (Mori.stalkAlgebra sM (s p)) V₁ V₂ _ _ _ _) :
    ((Module.finrank (ResidueField (M.presheaf.stalk (s p)))
        (CotangentSpace (M.presheaf.stalk (s p))) -
        (Module.finrank k V₁ + Module.finrank k V₂) : ℕ) : WithBot ℕ∞) ≤
      topologicalKrullDimAt M (s p) := by
  letI := Mori.stalkAlgebra sM (s p)
  have hfin := ProjectiveLineCriterion.finrank_residueField_of_section sM s hs p
  letI : Algebra k (M.residueField (s p)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sM.appTop ≫ M.Γevaluation (s p)).hom.toAlgebra
  have hk : Function.Bijective (algebraMap k (ResidueField (M.presheaf.stalk (s p)))) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hfin
  have hclosed : IsClosed ({s p} : Set M) := by
    have hfin' : Module.finrank k (M.residueField (s p)) = 1 := hfin
    refine isClosed_singleton_of_module_finite_residueField sM (s p) ?_
    exact Module.finite_of_finrank_pos (by rw [hfin']; exact one_pos)
  have := LocallyOfFiniteType.isLocallyNoetherian sM
  have : IsNoetherianRing (M.presheaf.stalk (s p)) := inferInstance
  rw [topologicalKrullDimAt_eq_krullDimOfRing_stalk k M sM (s p) hclosed]
  exact natCast_finrank_cotangentSpace_sub_le hk T

end Scheme

end MMP.Fourfold
