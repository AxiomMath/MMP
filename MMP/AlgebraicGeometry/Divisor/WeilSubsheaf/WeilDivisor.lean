/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.Basic

/-!
# Weil divisors and `ℚ`-Weil divisorial sheaves in *Flips and abundance*

The definitions of FA 16.1.2–16.1.3, 16.2.1–16.2.2 and 16.3.6: Weil divisors and `ℚ`-Weil
divisors (supported on the prime divisors along which `X` is a discrete valuation ring), the
sheaf `𝒪(D) ⊆ K(X)` of a Weil divisor and the twist `𝓛(D) = 𝓛 · 𝒪(D)`, the reflexive powers
`𝓛^[n]`, the `ℚ`-Weil divisorial sheaves `WSh(X)_ℚ`, and Weil divisorial sheaves with good
support on a closed subset `S ⊆ X`.

As in `MMP.Foundations.Flips.WeilSubsheaf`, the codimension of a point `η` of `X` is its coheight
`Order.coheight η` in the specialization order. For a point `P` of a closed subset `S`, the
codimension of `P` in `S` is the coheight of `⟨P, hP⟩ : S` in the specialization order of the
subspace `S`, which is the restriction of the specialization order of `X`.

## Main definitions

* `MMP.Flips.WeilDivisorPrime`: the prime divisors `Γ` of `X` with `𝒪_{X,Γ}` a DVR.
* `MMP.Flips.WeilDivisor`, `MMP.Flips.QWeilDivisor`: `WDiv(X)` and `WDiv(X)_ℚ` (FA 16.2.1).
* `MMP.Flips.WeilDivisor.sheaf`: `𝒪(D) ⊆ K(X)` (FA 16.2.2).
* `MMP.Flips.WeilDivisorialSubsheaf.twist`: `𝓛(D) = 𝓛 · 𝒪(D)` (FA 16.2.2).
* `MMP.Flips.RationalFunctionsSubmodule.reflexivePow`: `𝓛^[n]` (FA 16.1.2).
* `MMP.Flips.QWeilDivisorialSheaf`: `WSh(X)_ℚ` (FA 16.1.3).
* `MMP.Flips.WeilDivisorialSubsheaf.HasGoodSupport`: good support on `S` (FA 16.3.6).
* `MMP.Flips.goodSupportSubsheaves`, `MMP.Flips.goodSupportQSheaves`: `WSh_S(X)` and
  `WSh_S(X)_ℚ` (FA 16.3.6, 16.5).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.1–16.5
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.Flips

open MMP.Mori

variable {X : Scheme.{u}}

/-! ### Weil divisors -/

variable (X) in
/-- The prime divisors `Γ` of `X` whose local ring `𝒪_{X,Γ}` is a discrete valuation ring (the
index set of `WDiv(X)`, FA 16.2.1). Being a DVR includes being a domain, which Mathlib's
`IsDiscreteValuationRing` takes as an instance argument. -/
@[mmp "def_fa16a_weil_divisor"]
def WeilDivisorPrime : Type u :=
  {Γ : MMP.Mori.PrimeDivisor X // ∃ _ : IsDomain Γ.localRing, IsDiscreteValuationRing Γ.localRing}

variable (X) in
/-- A *Weil divisor* on `X` (FA 16.2.1): a finite formal sum `D = ∑ n_Γ Γ`, `n_Γ ∈ ℤ`, over the
prime divisors `Γ` of `X` such that `𝒪_{X,Γ}` is a discrete valuation ring. `WDiv(X)` is the group
of Weil divisors, the free abelian group on `WeilDivisorPrime X`.

This differs from `MMP.Mori.Divisor X`, which is free on all prime divisors; the two agree when
every `𝒪_{X,Γ}` is a DVR (`X` normal in codimension one). -/
@[mmp "def_fa16a_weil_divisor"]
abbrev WeilDivisor : Type u := WeilDivisorPrime X →₀ ℤ

variable (X) in
/-- A *`ℚ`-Weil divisor* on `X` (FA 16.2.1): a finite formal sum `∑ d_Γ Γ`, `d_Γ ∈ ℚ`, over the
same prime divisors `Γ` as for `WeilDivisor`. The group `WDiv(X)_ℚ = WDiv(X) ⊗_ℤ ℚ` is identified
with it by `WeilDivisor.tensorEquiv`. -/
@[mmp "def_fa16a_q_weil_divisor"]
abbrev QWeilDivisor : Type u := WeilDivisorPrime X →₀ ℚ

open scoped Classical in
variable (X) in
/-- `WDiv(X)_ℚ = WDiv(X) ⊗_ℤ ℚ` is the group of `ℚ`-Weil divisors (FA 16.2.1). -/
@[mmp "def_fa16a_q_weil_divisor"]
def WeilDivisor.tensorEquiv : TensorProduct ℤ (WeilDivisor X) ℚ ≃ₗ[ℤ] QWeilDivisor X :=
  TensorProduct.finsuppScalarLeft ℤ ℚ (WeilDivisorPrime X)

/-! ### Subsheaves of `K(X)` cut out by stalk conditions -/

/-- The germ at `x` of `r • s` is `r_x · s_x`, where `𝒪_{X,x}` acts on `K(X)_x` through the stalk
map of `𝒪_X ⟶ K(X)`. -/
theorem germ_smul_rationalFunctions {V : X.Opens} {x : X} (hx : x ∈ V) (r : Γ(X, V))
    (s : ToType ((rationalFunctionsPresheaf X).obj (op V))) :
    (rationalFunctionsPresheaf X).germ V x hx (r • s) =
      (structureStalkToRationalFunctionsStalk X x).hom (X.presheaf.germ V x hx r) *
        (rationalFunctionsPresheaf X).germ V x hx s := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx (toRationalFunctionsPresheaf X) r).symm

namespace RationalFunctionsSubmodule

/-- The `𝒪_X`-submodule of `K(X)` whose sections over `V` are the `s ∈ K(X)(V)` whose germ at
every point `x ∈ V` satisfies a condition `P x`, closed under `0`, sums and multiplication by the
image of `𝒪_{X,x}` in `K(X)_x`. -/
def ofStalkCondition (P : ∀ x : X, (rationalFunctionsPresheaf X).stalk x → Prop)
    (zero : ∀ x, P x 0) (add : ∀ x a b, P x a → P x b → P x (a + b))
    (mul : ∀ x (r : X.presheaf.stalk x) a, P x a →
      P x ((structureStalkToRationalFunctionsStalk X x).hom r * a)) :
    RationalFunctionsSubmodule X where
  sections V :=
    { carrier := {s | ∀ (x : X) (hx : x ∈ V), P x ((rationalFunctionsPresheaf X).germ V x hx s)}
      zero_mem' := fun x hx => by simpa using zero x
      add_mem' := fun hs ht x hx => by rw [map_add]; exact add x _ _ (hs x hx) (ht x hx)
      smul_mem' := fun r s hs x hx => by
        rw [germ_smul_rationalFunctions]; exact mul x _ _ (hs x hx) }
  map_mem := by
    intro U V i s hs x hx
    rw [TopCat.Presheaf.germ_res_apply]
    exact hs x (i.le hx)
  mem_of_locally := by
    intro U s hs x hx
    obtain ⟨W, i, hxW, h⟩ := hs x hx
    simpa only [TopCat.Presheaf.germ_res_apply] using h x hxW

end RationalFunctionsSubmodule

/-! ### The sheaf `𝒪(D)` -/

namespace WeilDivisor

/-- The condition on a germ `g ∈ K(X)_x` defining `𝒪(D)` (FA 16.2.2):
* if `x` is the generic point of a prime divisor `Γ` with `𝒪_{X,Γ}` a DVR, then
  `g ∈ t^{-n_Γ} 𝒪_{X,Γ}` for every uniformizer `t` of `𝒪_{X,Γ}`, in the form
  `t^{n_Γ} g ∈ 𝒪_{X,Γ}` if `n_Γ ≥ 0` and `g ∈ t^{-n_Γ} 𝒪_{X,Γ}` if `n_Γ < 0`, that is,
  `t^{max(n_Γ, 0)} g = t^{max(-n_Γ, 0)} a` for some `a ∈ 𝒪_{X,Γ}`;
* if `x` is any other point of codimension `≤ 1`, then `g ∈ 𝒪_{X,x}`;
* there is no condition at the points of codimension `≥ 2`.
Here `𝒪_{X,x}` is mapped to `K(X)_x` by the stalk map of `𝒪_X ⟶ K(X)`. -/
def StalkCondition (D : WeilDivisor X) (x : X) (g : (rationalFunctionsPresheaf X).stalk x) :
    Prop :=
  (∀ Γ : WeilDivisorPrime X, ∀ h : Γ.1.genericPoint = x, ∀ t : Γ.1.localRing, Irreducible t →
    ∃ a : X.presheaf.stalk x,
      (structureStalkToRationalFunctionsStalk X x).hom (h ▸ t) ^ (D Γ).toNat * g =
        (structureStalkToRationalFunctionsStalk X x).hom (h ▸ t) ^ (-D Γ).toNat *
          (structureStalkToRationalFunctionsStalk X x).hom a)
  ∧ (Order.coheight x ≤ 1 → (∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint ≠ x) →
      g ∈ Set.range (structureStalkToRationalFunctionsStalk X x).hom)

/-- The sheaf `𝒪(D) ⊆ K(X)` of a Weil divisor `D = ∑ n_Γ Γ` (FA 16.2.2, with the corrected sign):
its sections over `V` are the `s ∈ K(X)(V)` such that `s_Γ ∈ t_Γ^{-n_Γ} 𝒪_{X,Γ}` for every `Γ ∈ V`
(that is, with generic point in `V`) with `𝒪_{X,Γ}` a DVR with uniformizer `t_Γ`, and
`s_η ∈ 𝒪_{X,η}` for every other point `η ∈ V` of codimension `≤ 1` (`StalkCondition`).

The first condition is imposed for every uniformizer `t` of `𝒪_{X,Γ}` (an irreducible element of
the DVR; the condition does not depend on the choice of `t`). It is written without inverting `t`:
`t^{n_Γ} s_Γ ∈ 𝒪_{X,Γ}` if `n_Γ ≥ 0`, and `s_Γ ∈ t^{-n_Γ} 𝒪_{X,Γ}` if `n_Γ < 0`, the products being
taken in `K(X)_Γ` through the stalk map `𝒪_{X,Γ} → K(X)_Γ`. When the image of `t` in `K(X)_Γ` is a
unit (as it is when `K(X)_Γ` is the fraction field of `𝒪_{X,Γ}`), this is `s_Γ ∈ t^{-n_Γ} 𝒪_{X,Γ}`;
the form used here needs no such fact. No hypothesis on `X` is needed for the definition. -/
@[mmp "def_fa16a_sheaf_of_weil_divisor"]
def sheaf (D : WeilDivisor X) : RationalFunctionsSubmodule X :=
  RationalFunctionsSubmodule.ofStalkCondition D.StalkCondition
    (fun x => ⟨fun Γ h t _ => ⟨0, by rw [map_zero, mul_zero, mul_zero]⟩,
      fun _ _ => ⟨0, map_zero _⟩⟩)
    (fun x a b ha hb => ⟨fun Γ h t ht => by
        obtain ⟨a', ha'⟩ := ha.1 Γ h t ht
        obtain ⟨b', hb'⟩ := hb.1 Γ h t ht
        exact ⟨a' + b', by rw [map_add, mul_add, mul_add, ha', hb']⟩,
      fun hc hΓ => by
        obtain ⟨a', rfl⟩ := ha.2 hc hΓ
        obtain ⟨b', rfl⟩ := hb.2 hc hΓ
        exact ⟨a' + b', map_add _ _ _⟩⟩)
    (fun x r a ha => ⟨fun Γ h t ht => by
        obtain ⟨a', ha'⟩ := ha.1 Γ h t ht
        refine ⟨r * a', ?_⟩
        rw [map_mul, mul_left_comm, ha']
        ring,
      fun hc hΓ => by
        obtain ⟨a', rfl⟩ := ha.2 hc hΓ
        exact ⟨r * a', map_mul _ _ _⟩⟩)

end WeilDivisor

/-- The twist `𝓛(D) = 𝓛 · 𝒪(D) ⊆ K(X)` of a Weil divisorial subsheaf `𝓛` by a Weil divisor `D`
(FA 16.2.2), the product of FA 16.1.2. -/
@[mmp "def_fa16a_twist_subsheaf"]
def WeilDivisorialSubsheaf.twist (L : WeilDivisorialSubsheaf X) (D : WeilDivisor X) :
    RationalFunctionsSubmodule X :=
  L.toRationalFunctionsSubmodule.mul D.sheaf

/-! ### Reflexive powers -/

namespace RationalFunctionsSubmodule

/-- The reflexive powers `𝓛^[n]`, `n ≥ 0`, of an `𝒪_X`-submodule `𝓛 ⊆ K(X)` (FA 16.1.2):
`𝓛^[0] = sat(𝒪_X)` and `𝓛^[n] = 𝓛^[n-1] · 𝓛` for `n ≥ 1`. -/
def reflexivePowNat (L : RationalFunctionsSubmodule X) : ℕ → RationalFunctionsSubmodule X
  | 0 => (unit X).saturation
  | n + 1 => (L.reflexivePowNat n).mul L

/-- The reflexive powers `𝓛^[n]`, `n ∈ ℤ`, of an `𝒪_X`-submodule `𝓛 ⊆ K(X)` (FA 16.1.2, stated
there for a Weil divisorial subsheaf `𝓛`): `𝓛^[0] = sat(𝒪_X)`, `𝓛^[n] = 𝓛^[n-1] · 𝓛` for `n ≥ 1`,
and `𝓛^[n] = (𝓛⁻¹)^[-n]` for `n < 0`. -/
def reflexivePow (L : RationalFunctionsSubmodule X) : ℤ → RationalFunctionsSubmodule X
  | (n : ℕ) => L.reflexivePowNat n
  | Int.negSucc n => L.inv.reflexivePowNat (n + 1)

/-- For `n ≥ 0`, the integer reflexive power `𝓛^[n]` is the natural reflexive power `𝓛^[n]`. -/
@[simp]
theorem reflexivePow_natCast (L : RationalFunctionsSubmodule X) (n : ℕ) :
    L.reflexivePow n = L.reflexivePowNat n := rfl

/-! #### Stalks as `ℤ`-submodules of `K(X)_x` -/

/-- The stalk `𝓕_x ⊆ K(X)_x`, as an additive subgroup (a `ℤ`-submodule) of the ring `K(X)_x`. -/
def stalk (F : RationalFunctionsSubmodule X) (x : X) :
    Submodule ℤ ((rationalFunctionsPresheaf X).stalk x) where
  carrier := F.stalkSet x
  zero_mem' := ⟨⊤, trivial, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨V₁, h₁, s₁, hs₁, rfl⟩ ⟨V₂, h₂, s₂, hs₂, rfl⟩
    have hx : x ∈ V₁ ⊓ V₂ := ⟨h₁, h₂⟩
    refine ⟨V₁ ⊓ V₂, hx,
      (rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op s₁ +
        (rationalFunctionsPresheaf X).map (homOfLE inf_le_right).op s₂,
      add_mem (F.map_mem _ hs₁) (F.map_mem _ hs₂), ?_⟩
    rw [map_add, TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left) x hx,
      TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right) x hx]
  smul_mem' := by
    rintro c _ ⟨V, h, s, hs, rfl⟩
    exact ⟨V, h, c • s, zsmul_mem hs c, map_zsmul _ c s⟩

/-- A germ lies in the `ℤ`-submodule `𝓕_x` iff it lies in the set `𝓕_x`. -/
theorem mem_stalk {F : RationalFunctionsSubmodule X} {x : X}
    {g : (rationalFunctionsPresheaf X).stalk x} : g ∈ F.stalk x ↔ g ∈ F.stalkSet x := Iff.rfl

/-- The germ at `x ∈ V` of a section of `𝓕` over `V` lies in the stalk `𝓕_x`. -/
theorem germ_mem_stalk (F : RationalFunctionsSubmodule X) {V : X.Opens} {x : X} (hx : x ∈ V)
    {s : ToType ((rationalFunctionsPresheaf X).obj (op V))} (hs : s ∈ F.sections V) :
    (rationalFunctionsPresheaf X).germ V x hx s ∈ F.stalk x := ⟨V, hx, s, hs, rfl⟩

/-- The sections of `𝓕` are sections of `sat(𝓕)`. -/
theorem sections_le_saturation (F : RationalFunctionsSubmodule X) (V : X.Opens) :
    F.sections V ≤ F.saturation.sections V :=
  fun s hs _ hη _ => ⟨V, hη, s, hs, rfl⟩

/-- At a point of codimension `≤ 1`, `sat(𝓕)` and `𝓕` have the same stalk. -/
theorem stalk_saturation (F : RationalFunctionsSubmodule X) {η : X}
    (hη : Order.coheight η ≤ 1) : F.saturation.stalk η = F.stalk η := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨V, hV, s, hs, rfl⟩
    exact hs η hV hη
  · rintro _ ⟨V, hV, s, hs, rfl⟩
    exact ⟨V, hV, s, F.sections_le_saturation V hs, rfl⟩

/-- Two saturations agree when the stalks agree at every point of codimension `≤ 1`. -/
theorem saturation_eq_of_stalk {F G : RationalFunctionsSubmodule X}
    (h : ∀ η : X, Order.coheight η ≤ 1 → F.stalk η = G.stalk η) :
    F.saturation = G.saturation := by
  ext V s
  simp only [mem_saturation_iff]
  exact forall₂_congr fun η hη => imp_congr_right fun hc => by
    rw [← mem_stalk, ← mem_stalk, h η hc]

/-- A section of `P(U)` is a section over `U` of the local closure of `P`. -/
theorem mem_localClosure_of_mem {P : ∀ U : X.Opens,
      Submodule Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U))} {hP} {U : X.Opens}
    {s : ToType ((rationalFunctionsPresheaf X).obj (op U))} (hs : s ∈ P U) :
    s ∈ (localClosure P hP).sections U :=
  fun _ hx => ⟨U, 𝟙 U, hx, by rwa [rationalFunctionsPresheaf_map_id_apply]⟩

/-- The stalk of the image `𝓕𝓖` of `𝓕 ⊗ 𝓖 → K(X)` is the product of the stalks. -/
theorem stalk_mulImage (F G : RationalFunctionsSubmodule X) (x : X) :
    (mulImage F G).stalk x = F.stalk x * G.stalk x := by
  refine le_antisymm ?_ (Submodule.mul_le.mpr ?_)
  · rintro _ ⟨V, hV, s, hs, rfl⟩
    obtain ⟨W, i, hxW, h⟩ := hs x hV
    rw [← TopCat.Presheaf.germ_res_apply _ i x hxW]
    refine Submodule.mul_induction_on h (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]
      exact Submodule.mul_mem_mul (F.germ_mem_stalk hxW ha) (G.germ_mem_stalk hxW hb)
    · rw [map_add]
      exact add_mem ha hb
  · rintro _ ⟨V₁, h₁, a, ha, rfl⟩ _ ⟨V₂, h₂, b, hb, rfl⟩
    have hx : x ∈ V₁ ⊓ V₂ := ⟨h₁, h₂⟩
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left : V₁ ⊓ V₂ ⟶ V₁) x hx,
      ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right : V₁ ⊓ V₂ ⟶ V₂) x hx,
      ← map_mul]
    exact germ_mem_stalk _ _ (mem_localClosure_of_mem
      (Submodule.mul_mem_mul (F.map_mem _ ha) (G.map_mem _ hb)))

/-- Multiplying the stalk of `𝓕` by the stalk of `𝒪_X` gives the stalk of `𝓕`. -/
theorem stalk_unit_mul (F : RationalFunctionsSubmodule X) (x : X) :
    (unit X).stalk x * F.stalk x = F.stalk x := by
  refine le_antisymm (Submodule.mul_le.mpr ?_) fun g hg => ?_
  · rintro _ ⟨V₁, h₁, a, ha, rfl⟩ _ ⟨V₂, h₂, b, hb, rfl⟩
    obtain ⟨W, i, hxW, h⟩ := ha x h₁
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp h
    have hx : x ∈ W ⊓ V₂ := ⟨hxW, h₂⟩
    rw [← TopCat.Presheaf.germ_res_apply _ i x hxW,
      ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left : W ⊓ V₂ ⟶ W) x hx,
      ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right : W ⊓ V₂ ⟶ V₂) x hx,
      ← map_mul, ← hr, rationalFunctionsPresheaf_map_algebraMap, ← Algebra.smul_def]
    exact germ_mem_stalk _ _ (Submodule.smul_mem _ _ (F.map_mem _ hb))
  · have h1 : (1 : (rationalFunctionsPresheaf X).stalk x) ∈ (unit X).stalk x :=
      ⟨⊤, trivial, 1, mem_localClosure_of_mem (Submodule.mem_one.mpr ⟨1, map_one _⟩), map_one _⟩
    simpa using Submodule.mul_mem_mul h1 hg

/-- At a point of codimension `≤ 1`, the stalk of `𝓛^[n+1]` is the `(n+1)`-st power of the
stalk of `𝓛`. -/
theorem stalk_reflexivePowNat_succ (L : RationalFunctionsSubmodule X) {η : X}
    (hη : Order.coheight η ≤ 1) (n : ℕ) :
    (L.reflexivePowNat (n + 1)).stalk η = L.stalk η ^ (n + 1) := by
  induction n with
  | zero =>
    change (mulImage (unit X).saturation L).saturation.stalk η = _
    rw [stalk_saturation _ hη, stalk_mulImage, stalk_saturation _ hη, stalk_unit_mul, zero_add,
      pow_one]
  | succ n ih =>
    change (mulImage _ L).saturation.stalk η = _
    rw [stalk_saturation _ hη, stalk_mulImage, ih, pow_succ _ (n + 1)]

/-- Two reflexive powers of positive exponents agree when the corresponding powers of the
stalks agree at every point of codimension `≤ 1`. -/
theorem reflexivePowNat_eq_of_stalk (L L' : RationalFunctionsSubmodule X) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ∀ η : X, Order.coheight η ≤ 1 → L.stalk η ^ a = L'.stalk η ^ b) :
    L.reflexivePowNat a = L'.reflexivePowNat b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hb
  refine saturation_eq_of_stalk fun η hη => ?_
  rw [← stalk_saturation _ hη, ← stalk_saturation (mulImage _ L') hη]
  exact (L.stalk_reflexivePowNat_succ hη a).trans ((h η hη).trans
    (L'.stalk_reflexivePowNat_succ hη b).symm)

/-- The stalks of equal reflexive powers of positive exponents. -/
theorem stalk_pow_eq_of_reflexivePowNat_eq {L L' : RationalFunctionsSubmodule X} {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (h : L.reflexivePowNat a = L'.reflexivePowNat b) {η : X}
    (hη : Order.coheight η ≤ 1) : L.stalk η ^ a = L'.stalk η ^ b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hb
  rw [← L.stalk_reflexivePowNat_succ hη, ← L'.stalk_reflexivePowNat_succ hη, h]

end RationalFunctionsSubmodule

/-! ### `ℚ`-Weil divisorial sheaves -/

namespace WeilDivisorialSubsheaf

open RationalFunctionsSubmodule

/-- The relation of FA 16.1.3 on pairs `(𝓛, n)` with `𝓛 ∈ WSh(X)` and `n ≥ 1`:
`(𝓛, n) ∼ (𝓛', n')` iff `𝓛^[mn'] = 𝓛'^[mn]` (as subsheaves of `K(X)`) for some `m ≥ 1`. -/
@[mmp "def_fa16a_q_weil_divisorial_sheaves"]
def QRel (p q : WeilDivisorialSubsheaf X × ℕ+) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ p.1.toRationalFunctionsSubmodule.reflexivePow (m * q.2 : ℕ) =
    q.1.toRationalFunctionsSubmodule.reflexivePow (m * p.2 : ℕ)

/-- The relation `QRel` on pairs `(𝓛, n)` is an equivalence relation. -/
theorem qRel_equivalence : Equivalence (QRel (X := X)) where
  refl p := ⟨1, le_rfl, rfl⟩
  symm := fun ⟨m, hm, h⟩ => ⟨m, hm, h.symm⟩
  trans := by
    rintro ⟨L, n⟩ ⟨L', n'⟩ ⟨L'', n''⟩ ⟨m, hm, h₁⟩ ⟨k, hk, h₂⟩
    simp only [reflexivePow_natCast] at h₁ h₂ ⊢
    have hn : 0 < (n : ℕ) := n.pos
    have hn' : 0 < (n' : ℕ) := n'.pos
    have hn'' : 0 < (n'' : ℕ) := n''.pos
    refine ⟨m * k * n', Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
    refine reflexivePowNat_eq_of_stalk _ _ (Nat.one_le_iff_ne_zero.mpr (by positivity))
      (Nat.one_le_iff_ne_zero.mpr (by positivity)) fun η hη => ?_
    have e₁ := stalk_pow_eq_of_reflexivePowNat_eq (Nat.one_le_iff_ne_zero.mpr (by positivity))
      (Nat.one_le_iff_ne_zero.mpr (by positivity)) h₁ hη
    have e₂ := stalk_pow_eq_of_reflexivePowNat_eq (Nat.one_le_iff_ne_zero.mpr (by positivity))
      (Nat.one_le_iff_ne_zero.mpr (by positivity)) h₂ hη
    calc L.stalk η ^ (m * k * n' * n'') = (L.stalk η ^ (m * n')) ^ (k * n'') := by ring
      _ = (L'.stalk η ^ (k * n'')) ^ (m * n) := by rw [e₁]; ring
      _ = L''.stalk η ^ (m * k * n' * n) := by rw [e₂]; ring

/-- The equivalence relation of FA 16.1.3 on pairs `(𝓛, n)`, `𝓛 ∈ WSh(X)`, `n ≥ 1`. -/
@[mmp "def_fa16a_q_weil_divisorial_sheaves"]
def qSetoid : Setoid (WeilDivisorialSubsheaf X × ℕ+) :=
  ⟨QRel, qRel_equivalence⟩

end WeilDivisorialSubsheaf

variable (X) in
/-- `WSh(X)_ℚ`, the *`ℚ`-Weil divisorial sheaves* (FA 16.1.3): the equivalence classes `[𝓛, n]` of
pairs `(𝓛, n)` with `𝓛 ∈ WSh(X)` and `n ∈ ℤ_{≥ 1}`, where `(𝓛, n) ∼ (𝓛', n')` iff
`𝓛^[mn'] = 𝓛'^[mn]` for some `m ∈ ℤ_{≥ 1}` (`WeilDivisorialSubsheaf.QRel`). -/
@[mmp "def_fa16a_q_weil_divisorial_sheaves"]
def QWeilDivisorialSheaf : Type u :=
  Quotient (WeilDivisorialSubsheaf.qSetoid (X := X))

/-- The class `(1/n)𝓛 = [𝓛, n] ∈ WSh(X)_ℚ` of a pair `(𝓛, n)`, `n ≥ 1` (FA 16.1.3). -/
@[mmp "def_fa16a_q_weil_divisorial_sheaves"]
def WeilDivisorialSubsheaf.divNat (L : WeilDivisorialSubsheaf X) (n : ℕ+) :
    QWeilDivisorialSheaf X :=
  Quotient.mk _ (L, n)

/-- `[𝓛, n] = [𝓛', n']` in `WSh(X)_ℚ` iff `𝓛^[mn'] = 𝓛'^[mn]` for some `m ≥ 1`. -/
theorem WeilDivisorialSubsheaf.divNat_eq_divNat_iff {L L' : WeilDivisorialSubsheaf X}
    {n n' : ℕ+} : L.divNat n = L'.divNat n' ↔
      ∃ m : ℕ, 1 ≤ m ∧ L.toRationalFunctionsSubmodule.reflexivePow (m * n' : ℕ) =
        L'.toRationalFunctionsSubmodule.reflexivePow (m * n : ℕ) :=
  Quotient.eq (r := WeilDivisorialSubsheaf.qSetoid)

/-! ### Good support -/

namespace RationalFunctionsSubmodule

/-- An `𝒪_X`-submodule `𝓕 ⊆ K(X)` is *invertible at* `x` if its stalk is a free `𝒪_{X,x}`-module
of rank one inside `K(X)_x`: `𝓕_x = f · 𝒪_{X,x}` for a unit `f` of `K(X)_x` (as in
`WeilDivisorialSubsheaf.principal_codim_one`). -/
def IsInvertibleAt (F : RationalFunctionsSubmodule X) (x : X) : Prop :=
  ∃ f : ((rationalFunctionsPresheaf X).stalk x)ˣ,
    F.stalkSet x = Set.range fun a : X.presheaf.stalk x =>
      (f : (rationalFunctionsPresheaf X).stalk x) *
        (structureStalkToRationalFunctionsStalk X x).hom a

end RationalFunctionsSubmodule

namespace WeilDivisorialSubsheaf

/-- A Weil divisorial subsheaf `𝓛` *has good support* on a closed subset `S ⊆ X` (FA 16.3.6) if
(i) `𝓛` is `ℚ`-Cartier at every point `P ∈ S` of codimension one in `S` (coheight `1` in the
specialization order of the subspace `S`): `𝓛^[n]` is invertible at `P` for some `n ≥ 1`; and
(ii) `S` and `Supp(𝓛)` have no common irreducible component: no generic point `ξ` of an irreducible
component of `S` (a point whose closure is a maximal irreducible subset of `S`) lies in
`Supp(𝓛)`. -/
@[mmp "def_fa16a_good_support"]
def HasGoodSupport (L : WeilDivisorialSubsheaf X) (S : Closeds X) : Prop :=
  (∀ P : S, Order.coheight P = 1 →
    ∃ n : ℕ, 1 ≤ n ∧ (L.toRationalFunctionsSubmodule.reflexivePow n).IsInvertibleAt P.1) ∧
  (∀ ξ : X, Maximal (fun T : Set X => T ⊆ S ∧ IsIrreducible T) (closure {ξ}) →
    ξ ∉ L.support)

end WeilDivisorialSubsheaf

/-- `WSh_S(X) ⊆ WSh(X)`, the Weil divisorial subsheaves with good support on the closed subset
`S` (FA 16.3.6). -/
@[mmp "def_fa16a_wsh_good_support_subgroup"]
def goodSupportSubsheaves (S : Closeds X) : Set (WeilDivisorialSubsheaf X) :=
  {L | L.HasGoodSupport S}

/-- `WSh_S(X)_ℚ ⊆ WSh(X)_ℚ`, the classes `(1/n)𝓛` with `n ≥ 1` and `𝓛 ∈ WSh_S(X)`
(FA 16.3.6, 16.5). -/
@[mmp "def_fa16a_wsh_good_support_subgroup_q"]
def goodSupportQSheaves (S : Closeds X) : Set (QWeilDivisorialSheaf X) :=
  {c | ∃ (L : WeilDivisorialSubsheaf X) (n : ℕ+), L ∈ goodSupportSubsheaves S ∧ c = L.divNat n}

end MMP.Flips
