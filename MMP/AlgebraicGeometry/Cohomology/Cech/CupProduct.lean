module

public import MMP.AlgebraicGeometry.Cohomology.Cech.ComplexMap

/-!
# The cup product on Čech cochains and morphisms into the derived category

Let `V` be a scheme, `𝒰 = (U α)` an open cover of `V` and `K` a cochain complex of
`𝒪_V`-modules. On an open `W`, a Čech cochain of bidegree `(p, m)` is a family of sections of
`K^p` over `W ∩ U_{x₀} ∩ ⋯ ∩ U_{x_m}`, one for every tuple `x` of `m + 1` indices; the total
cochains of degree `n` carry the total differential `D = d_K + (-1)^p δ`. A product on the
sections of `K` satisfying the Leibniz rule (for instance the wedge product on a de Rham complex)
induces, through the Alexander–Whitney formula
`(x ⌣ y)_{z₀ ⋯ z_m} = x_{z₀ ⋯ z_{m₁}} · y_{z_{m₁} ⋯ z_m}`, a cup product on total cochains, and
`D (c ⌣ c') = D c ⌣ c' + (-1)^n c ⌣ D c'`. In particular cup products of cocycles are cocycles,
and the component of bidegree `(n + n', 0)` of `c ⌣ c'` is the product of the components of
bidegrees `(n, 0)` and `(n', 0)`.

A family of morphisms `g^{p,m} : M ⟶ Č^m(𝒰, K^p)`, `p + m = n`, whose sections form total
cocycles on every open (`MMP.DeRham.CechCocycleData`) defines a morphism of complexes
`M[-n] ⟶ Tot Č(𝒰, K)` and hence, for `K` bounded below, a morphism `M[-n] ⟶ K` in the derived
category. On an open `W ⊆ U α` the induced map `M ⟶ ℋ^n(K)` sends a section to the class of its
component of bidegree `(n, 0)` at `α`: the Čech complex is contractible on `W` by
`(k c)_{x₀ ⋯ x_m} = c_{α x₀ ⋯ x_m}`, so a total cocycle is cohomologous there to that component.

## Main definitions

* `MMP.DeRham.CechCochain`, `MMP.DeRham.CechTotalCochain`: Čech cochains of sections of
  bidegree `(p, m)` and of total degree `n`, with `CechCochain.delta`, `CechCochain.horiz` and
  `CechTotalCochain.d`.
* `MMP.DeRham.SectionProduct`: a product on the sections of a complex with the Leibniz rule.
* `MMP.DeRham.CechCochain.aw`, `MMP.DeRham.CechTotalCochain.cup`: the Alexander–Whitney
  product and the cup product of total cochains; `MMP.DeRham.CechTotalCochain.cupFin`: the
  iterated cup product of cochains of degree `1`.
* `MMP.DeRham.CechCocycleData`: Čech cocycles of any total degree defined on a sheaf.
* `MMP.DeRham.CechCocycleData.cechMap`, `derivedMap`, `homologyMap`: the morphisms
  `M[-n] ⟶ Tot Č(𝒰, K)`, `M[-n] ⟶ K` in `D(V)` and `M ⟶ ℋ^n(K)`.

## Main results

* `MMP.DeRham.CechCochain.delta_aw`, `MMP.DeRham.CechCochain.horiz_aw`: the Leibniz rules of the
  Alexander–Whitney product.
* `MMP.DeRham.CechTotalCochain.d_cup`: the Leibniz rule for the cup product.
* `MMP.DeRham.CechTotalCochain.IsCocycle.cup`, `isCocycle_cupFin`, `cup_apply_zero`: cup
  products of cocycles are cocycles, with the expected component of Čech degree `0`.
* `MMP.DeRham.CechTotalCochain.eq_d_homotopy_succ`, `eq_d_homotopy_zero`: a cocycle on an open
  inside a member of the cover is a coboundary up to its component at that member.
* `MMP.DeRham.CechCocycleData.homologyMap_app_eq`: the local description of the cohomology map.
* `MMP.DeRham.CechCocycleData.homologyFunctor_map_derivedMap`: the cohomology in degree `n` of
  `derivedMap` is `homologyMap`.

## Implementation notes

All degrees enter through explicit equations (`a + b = c`, `p + m = n`) rather than through
arithmetic in the indices, so that no transport along equalities of degrees is needed; a total
cochain is a dependent function of a bidegree and of such an equation. The product on sections is
only asked to be biadditive, so it applies to the twisted module structure of a Frobenius direct
image. The Čech complex uses all tuples of indices, as in `MMP.DeRham.CechGluingData`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.CechSiteChange
open Stacks.CategoryTheory.CechComplex (inter interπ interMap)

universe u

namespace MMP.DeRham

variable {V : Scheme.{u}} {ι : Type u} (U : ι → V.Opens)

/-! ### Čech cochains of sections -/

variable (K : CochainComplex V.Modules ℤ) (W : V.Opens)

/-- **Čech cochains of bidegree `(p, m)` of `K` on `W`**: a section of `K^p` over
`W ⊓ U_{x₀} ⊓ ⋯ ⊓ U_{x_m}` for every tuple `x` of `m + 1` indices. -/
abbrev CechCochain (p : ℤ) (m : ℕ) : Type u :=
  ∀ x : Fin (m + 1) → ι, Γ(K.X p, W ⊓ inter U x)

variable {U K W}

/-- The intersection over a tuple `z` is contained in the intersection over `z ∘ g`. -/
theorem inf_inter_le_comp {m m' : ℕ} (z : Fin m' → ι) (g : Fin m → Fin m') :
    W ⊓ inter U z ≤ W ⊓ inter U (z ∘ g) :=
  inf_le_inf_left W (leOfHom (interMap U z g))

namespace CechCochain

variable {p : ℤ} {m : ℕ}

/-- The pullback of a cochain along a map of index tuples: the restriction of the component at
`z ∘ g` to `W ⊓ inter U z`. -/
def pull (c : CechCochain U K W p m) {m' : ℕ} (z : Fin m' → ι) (g : Fin (m + 1) → Fin m') :
    Γ(K.X p, W ⊓ inter U z) :=
  (K.X p).presheaf.map (homOfLE (inf_inter_le_comp z g)).op (c (z ∘ g))

/-- Pullbacks along equal maps of index tuples are equal. -/
theorem pull_congr (c : CechCochain U K W p m) {m' : ℕ} (z : Fin m' → ι)
    {g g' : Fin (m + 1) → Fin m'} (h : g = g') : c.pull z g = c.pull z g' := by
  subst h
  rfl

/-- The pullback along the identity is the component itself. -/
theorem pull_id (c : CechCochain U K W p m) (z : Fin (m + 1) → ι) : c.pull z id = c z :=
  presheaf_map_id _ _

/-- Restricting the pullback along `g` at `z ∘ h` to `W ⊓ inter U z` gives the pullback along
`h ∘ g` at `z`. -/
theorem map_pull (c : CechCochain U K W p m) {m' m'' : ℕ} (z : Fin m'' → ι)
    (h : Fin m' → Fin m'') (g : Fin (m + 1) → Fin m') :
    (K.X p).presheaf.map (homOfLE (inf_inter_le_comp z h)).op (c.pull (z ∘ h) g) =
      c.pull z (h ∘ g) :=
  presheaf_map_map _ _ _ _

/-- The pullback is additive. -/
theorem pull_add (c c' : CechCochain U K W p m) {m' : ℕ} (z : Fin m' → ι)
    (g : Fin (m + 1) → Fin m') : (c + c').pull z g = c.pull z g + c'.pull z g :=
  map_add _ _ _

/-- The pullback commutes with multiplication by an integer. -/
theorem pull_zsmul (k : ℤ) (c : CechCochain U K W p m) {m' : ℕ} (z : Fin m' → ι)
    (g : Fin (m + 1) → Fin m') : (k • c).pull z g = k • c.pull z g :=
  map_zsmul _ _ _

/-- The pullback commutes with finite sums. -/
theorem pull_sum {α : Type*} (s : Finset α) (c : α → CechCochain U K W p m) {m' : ℕ}
    (z : Fin m' → ι) (g : Fin (m + 1) → Fin m') :
    (∑ a ∈ s, c a).pull z g = ∑ a ∈ s, (c a).pull z g := by
  unfold pull
  rw [Finset.sum_apply, map_sum]

end CechCochain

/-! ### Face maps and segments -/

/-- The face map `Fin (m + 1) → Fin (m + 2)` omitting `i`. -/
def face (m i : ℕ) : Fin (m + 1) → Fin (m + 2) :=
  fun k ↦ ⟨if (k : ℕ) < i then k else k + 1, by split_ifs <;> omega⟩

/-- `Fin.succAbove i` is the face map omitting `i`. -/
theorem succAbove_eq_face {m : ℕ} (i : Fin (m + 2)) : i.succAbove = face m i := by
  funext k
  ext
  unfold Fin.succAbove face
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

/-- The segment `j ↦ s + j` of length `l + 1` in `Fin (m + 1)`. -/
def seg (s l m : ℕ) (h : s + l ≤ m) : Fin (l + 1) → Fin (m + 1) :=
  fun j ↦ ⟨s + j, by omega⟩

namespace CechCochain

variable {p : ℤ} {m : ℕ}

/-- **The Čech differential** of cochains of sections:
`(δ c)_{z₀ ⋯ z_{m+1}} = ∑ᵢ (-1)ⁱ c_{z₀ ⋯ ẑᵢ ⋯ z_{m+1}}`. -/
def delta (c : CechCochain U K W p m) : CechCochain U K W p (m + 1) :=
  fun z ↦ ∑ i ∈ Finset.range (m + 2), ((-1 : ℤ) ^ i) • c.pull z (face m i)

/-- The pullback of `δ c` along `g` is the alternating sum of the pullbacks of `c` along the
composites of `g` with the face maps. -/
theorem delta_pull (c : CechCochain U K W p m) {m' : ℕ} (z : Fin m' → ι)
    (g : Fin (m + 2) → Fin m') :
    c.delta.pull z g = ∑ i ∈ Finset.range (m + 2), ((-1 : ℤ) ^ i) • c.pull z (g ∘ face m i) := by
  unfold pull delta
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul]
  exact congrArg _ (c.map_pull z g (face m i))

/-- The Čech differential is additive. -/
theorem delta_add (c c' : CechCochain U K W p m) : (c + c').delta = c.delta + c'.delta := by
  funext z
  simp only [delta, pull_add, smul_add, Finset.sum_add_distrib, Pi.add_apply]

/-- The Čech differential commutes with multiplication by an integer. -/
theorem delta_zsmul (k : ℤ) (c : CechCochain U K W p m) : (k • c).delta = k • c.delta := by
  funext z
  simp only [delta, pull_zsmul, smul_comm _ k, Finset.smul_sum, Pi.smul_apply]

/-- The Čech differential commutes with finite sums. -/
theorem delta_sum {α : Type*} (s : Finset α) (c : α → CechCochain U K W p m) :
    (∑ a ∈ s, c a).delta = ∑ a ∈ s, (c a).delta := by
  funext z
  simp only [delta, pull_sum, Finset.smul_sum, Finset.sum_apply]
  exact Finset.sum_comm

/-- The Čech differential of `0` is `0`. -/
theorem delta_zero : (0 : CechCochain U K W p m).delta = 0 := by
  simpa using delta_zsmul (U := U) (K := K) (W := W) (p := p) (m := m) 0 0

/-- The differential of `K` applied to every component of a cochain. -/
def horiz (p p' : ℤ) (c : CechCochain U K W p m) : CechCochain U K W p' m :=
  fun x ↦ (K.d p p').app _ (c x)

/-- The differential of `K` commutes with pullbacks. -/
theorem horiz_pull (p p' : ℤ) (c : CechCochain U K W p m) {m' : ℕ} (z : Fin m' → ι)
    (g : Fin (m + 1) → Fin m') : (horiz p p' c).pull z g = (K.d p p').app _ (c.pull z g) :=
  (app_presheaf_map _ _ _).symm

/-- `horiz` is additive. -/
theorem horiz_add (p p' : ℤ) (c c' : CechCochain U K W p m) :
    horiz p p' (c + c') = horiz p p' c + horiz p p' c' := by
  funext x
  exact map_add _ _ _

/-- `horiz` commutes with multiplication by an integer. -/
theorem horiz_zsmul (p p' : ℤ) (k : ℤ) (c : CechCochain U K W p m) :
    horiz p p' (k • c) = k • horiz p p' c := by
  funext x
  exact map_zsmul _ _ _

/-- `horiz` commutes with finite sums. -/
theorem horiz_sum (p p' : ℤ) {α : Type*} (s : Finset α) (c : α → CechCochain U K W p m) :
    horiz p p' (∑ a ∈ s, c a) = ∑ a ∈ s, horiz p p' (c a) := by
  funext x
  simp only [horiz, Finset.sum_apply]
  exact map_sum _ _ _

/-- `horiz` sends `0` to `0`. -/
theorem horiz_zero (p p' : ℤ) : horiz p p' (0 : CechCochain U K W p m) = 0 := by
  simpa using horiz_zsmul (U := U) (K := K) (W := W) (m := m) p p' 0 0

/-- The differential of `K` commutes with the Čech differential. -/
theorem horiz_delta (p p' : ℤ) (c : CechCochain U K W p m) :
    horiz p p' c.delta = (horiz p p' c).delta := by
  funext z
  simp only [horiz, delta, horiz_pull]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ map_zsmul _ _ _

end CechCochain

/-! ### Products on the sections of a complex -/

variable (K) in
/-- **A product on the sections of a complex** `K` of sheaves: biadditive maps
`Γ(K^a, A) × Γ(K^b, A) → Γ(K^{a+b}, A)` on every open `A`, compatible with restriction and
satisfying the Leibniz rule `d (x y) = (d x) y + (-1)^a x (d y)`. The target degree is a separate
index `c` with `a + b = c`, so that no transport along equalities of degrees is needed. -/
structure SectionProduct where
  /-- The product. -/
  mul (a b c : ℤ) (h : a + b = c) (A : V.Opens) : Γ(K.X a, A) →+ Γ(K.X b, A) →+ Γ(K.X c, A)
  /-- The product commutes with restriction. -/
  map_mul (a b c : ℤ) (h : a + b = c) {A B : V.Opens} (i : B ≤ A) (x : Γ(K.X a, A))
    (y : Γ(K.X b, A)) :
    (K.X c).presheaf.map (homOfLE i).op (mul a b c h A x y) =
      mul a b c h B ((K.X a).presheaf.map (homOfLE i).op x) ((K.X b).presheaf.map (homOfLE i).op y)
  /-- The Leibniz rule. -/
  d_mul (a a' b b' c c' : ℤ) (h : a + b = c) (ha : a + 1 = a') (hb : b + 1 = b')
    (hc : c + 1 = c') (A : V.Opens) (x : Γ(K.X a, A)) (y : Γ(K.X b, A)) :
    (K.d c c').app A (mul a b c h A x y) =
      mul a' b c' (by omega) A ((K.d a a').app A x) y +
        (a.negOnePow : ℤ) • mul a b' c' (by omega) A x ((K.d b b').app A y)

namespace CechCochain

variable (μ : SectionProduct K) {a b c : ℤ} (h : a + b = c) {m₁ m₂ m : ℕ}

/-- **The Alexander–Whitney product** of Čech cochains:
`(x ⌣ y)_{z₀ ⋯ z_m} = x_{z₀ ⋯ z_{m₁}} · y_{z_{m₁} ⋯ z_m}` for `m₁ + m₂ = m`. -/
def aw (hm : m₁ + m₂ = m) (x : CechCochain U K W a m₁) (y : CechCochain U K W b m₂) :
    CechCochain U K W c m :=
  fun z ↦ μ.mul a b c h _ (x.pull z (seg 0 m₁ m (by omega))) (y.pull z (seg m₁ m₂ m (by omega)))

/-- The pullback of `x ⌣ y` along `g` is the product of the pullbacks of `x` and `y` along the
composites of `g` with the front and back segments. -/
theorem aw_pull (hm : m₁ + m₂ = m) (x : CechCochain U K W a m₁) (y : CechCochain U K W b m₂)
    {m' : ℕ} (z : Fin m' → ι) (g : Fin (m + 1) → Fin m') :
    (aw μ h hm x y).pull z g = μ.mul a b c h _ (x.pull z (g ∘ seg 0 m₁ m (by omega)))
      (y.pull z (g ∘ seg m₁ m₂ m (by omega))) :=
  (μ.map_mul _ _ _ _ _ _ _).trans (congrArg₂ (fun u v ↦ μ.mul a b c h _ u v)
    (map_pull x z g (seg 0 m₁ m (by omega))) (map_pull y z g (seg m₁ m₂ m (by omega))))

/-- The Alexander–Whitney product is compatible with transport of its factors along equalities
of Čech degrees. -/
theorem aw_congr {m₁' m₂' : ℕ} (hm : m₁ + m₂ = m) (hm' : m₁' + m₂' = m) (e₁ : m₁ = m₁')
    (e₂ : m₂ = m₂') (x : CechCochain U K W a m₁) (y : CechCochain U K W b m₂)
    (x' : CechCochain U K W a m₁') (y' : CechCochain U K W b m₂') (ex : e₁ ▸ x = x')
    (ey : e₂ ▸ y = y') : aw μ h hm x y = aw μ h hm' x' y' := by
  subst e₁ e₂ ex ey
  rfl

/-- The Alexander–Whitney product is additive in its first factor. -/
theorem aw_add_left (hm : m₁ + m₂ = m) (x x' : CechCochain U K W a m₁)
    (y : CechCochain U K W b m₂) : aw μ h hm (x + x') y = aw μ h hm x y + aw μ h hm x' y := by
  funext z
  simp only [aw, pull_add, map_add, AddMonoidHom.add_apply, Pi.add_apply]

/-- The Alexander–Whitney product is additive in its second factor. -/
theorem aw_add_right (hm : m₁ + m₂ = m) (x : CechCochain U K W a m₁)
    (y y' : CechCochain U K W b m₂) : aw μ h hm x (y + y') = aw μ h hm x y + aw μ h hm x y' := by
  funext z
  simp only [aw, pull_add, map_add, Pi.add_apply]

/-- The Alexander–Whitney product commutes with integer multiples in its first factor. -/
theorem aw_zsmul_left (hm : m₁ + m₂ = m) (k : ℤ) (x : CechCochain U K W a m₁)
    (y : CechCochain U K W b m₂) : aw μ h hm (k • x) y = k • aw μ h hm x y := by
  funext z
  simp only [aw, pull_zsmul, map_zsmul, AddMonoidHom.smul_apply, Pi.smul_apply]

/-- The Alexander–Whitney product commutes with integer multiples in its second factor. -/
theorem aw_zsmul_right (hm : m₁ + m₂ = m) (k : ℤ) (x : CechCochain U K W a m₁)
    (y : CechCochain U K W b m₂) : aw μ h hm x (k • y) = k • aw μ h hm x y := by
  funext z
  simp only [aw, pull_zsmul, map_zsmul, Pi.smul_apply]

/-- The Alexander–Whitney product commutes with finite sums in its first factor. -/
theorem aw_sum_left {α : Type*} (s : Finset α) (hm : m₁ + m₂ = m)
    (x : α → CechCochain U K W a m₁) (y : CechCochain U K W b m₂) :
    aw μ h hm (∑ i ∈ s, x i) y = ∑ i ∈ s, aw μ h hm (x i) y := by
  funext z
  simp only [aw, pull_sum, map_sum, AddMonoidHom.finsetSum_apply, Finset.sum_apply]

/-- The Alexander–Whitney product commutes with finite sums in its second factor. -/
theorem aw_sum_right {α : Type*} (s : Finset α) (hm : m₁ + m₂ = m)
    (x : CechCochain U K W a m₁) (y : α → CechCochain U K W b m₂) :
    aw μ h hm x (∑ i ∈ s, y i) = ∑ i ∈ s, aw μ h hm x (y i) := by
  funext z
  simp only [aw, pull_sum, map_sum, Finset.sum_apply]

/-- The Alexander–Whitney product with first factor `0` is `0`. -/
theorem aw_zero_left (hm : m₁ + m₂ = m) (y : CechCochain U K W b m₂) :
    aw μ h hm (0 : CechCochain U K W a m₁) y = 0 := by
  simpa using aw_zsmul_left μ h hm 0 0 y

/-- The Alexander–Whitney product with second factor `0` is `0`. -/
theorem aw_zero_right (hm : m₁ + m₂ = m) (x : CechCochain U K W a m₁) :
    aw μ h hm x (0 : CechCochain U K W b m₂) = 0 := by
  simpa using aw_zsmul_right μ h hm 0 x 0

/-- **The Leibniz rule for the differential of `K`.** -/
theorem horiz_aw {a' b' c' : ℤ} (ha : a + 1 = a') (hb : b + 1 = b') (hc : c + 1 = c')
    (hm : m₁ + m₂ = m) (x : CechCochain U K W a m₁) (y : CechCochain U K W b m₂) :
    horiz c c' (aw μ h hm x y) = aw μ (by omega) hm (horiz a a' x) y +
      (a.negOnePow : ℤ) • aw μ (by omega) hm x (horiz b b' y) := by
  funext z
  simp only [horiz, aw, Pi.add_apply, Pi.smul_apply, horiz_pull]
  exact μ.d_mul a a' b b' c c' h ha hb hc _ _ _

/-- **The Leibniz rule for the Čech differential**:
`δ (x ⌣ y) = δ x ⌣ y + (-1)^{m₁} x ⌣ δ y`. -/
theorem delta_aw (hm : m₁ + m₂ = m) (x : CechCochain U K W a m₁) (y : CechCochain U K W b m₂) :
    (aw μ h hm x y).delta = aw μ h (by omega : m₁ + 1 + m₂ = m + 1) x.delta y +
      ((-1 : ℤ) ^ m₁) • aw μ h (by omega : m₁ + (m₂ + 1) = m + 1) x y.delta := by
  subst hm
  funext z
  simp only [delta, aw_pull, aw, Pi.add_apply, Pi.smul_apply, delta_pull, map_sum, map_zsmul,
    AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, Finset.smul_sum, smul_smul]
  rw [show Finset.range (m₁ + m₂ + 2) = Finset.range ((m₁ + 1) + (m₂ + 1)) from
      congrArg Finset.range (by omega),
    Finset.sum_range_add, Finset.sum_range_succ _ (m₁ + 1), Finset.sum_range_succ' _ (m₂ + 1)]
  have e1 : ∀ i ∈ Finset.range (m₁ + 1),
      ((-1 : ℤ) ^ i) • μ.mul a b c h _ (x.pull z (face (m₁ + m₂) i ∘ seg 0 m₁ _ (by omega)))
        (y.pull z (face (m₁ + m₂) i ∘ seg m₁ m₂ _ (by omega))) =
      ((-1 : ℤ) ^ i) • μ.mul a b c h _ (x.pull z (seg 0 (m₁ + 1) _ (by omega) ∘ face m₁ i))
        (y.pull z (seg (m₁ + 1) m₂ _ (by omega))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have f1 : face (m₁ + m₂) i ∘ seg 0 m₁ _ (by omega) =
        seg 0 (m₁ + 1) _ (by omega) ∘ face m₁ i := by
      funext k
      apply Fin.ext
      unfold face seg
      dsimp only [Function.comp_apply]
      split_ifs <;> omega
    have f2 : face (m₁ + m₂) i ∘ seg m₁ m₂ _ (by omega) =
        seg (m₁ + 1) m₂ (m₁ + m₂ + 1) (by omega) := by
      funext k
      apply Fin.ext
      unfold face seg
      dsimp only [Function.comp_apply]
      split_ifs <;> omega
    rw [x.pull_congr z f1, y.pull_congr z f2]
  have e2 : ∀ i ∈ Finset.range (m₂ + 1),
      ((-1 : ℤ) ^ (m₁ + 1 + i)) • μ.mul a b c h _
        (x.pull z (face (m₁ + m₂) (m₁ + 1 + i) ∘ seg 0 m₁ _ (by omega)))
        (y.pull z (face (m₁ + m₂) (m₁ + 1 + i) ∘ seg m₁ m₂ _ (by omega))) =
      ((-1 : ℤ) ^ m₁ * (-1 : ℤ) ^ (i + 1)) • μ.mul a b c h _
        (x.pull z (seg 0 m₁ _ (by omega)))
        (y.pull z (seg m₁ (m₂ + 1) _ (by omega) ∘ face m₂ (i + 1))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show (-1 : ℤ) ^ m₁ * (-1 : ℤ) ^ (i + 1) = (-1 : ℤ) ^ (m₁ + 1 + i) by ring]
    have f1 : face (m₁ + m₂) (m₁ + 1 + i) ∘ seg 0 m₁ _ (by omega) =
        seg 0 m₁ (m₁ + m₂ + 1) (by omega) := by
      funext k
      apply Fin.ext
      unfold face seg
      dsimp only [Function.comp_apply]
      split_ifs <;> omega
    have f2 : face (m₁ + m₂) (m₁ + 1 + i) ∘ seg m₁ m₂ _ (by omega) =
        seg m₁ (m₂ + 1) (m₁ + m₂ + 1) (by omega) ∘ face m₂ (i + 1) := by
      funext k
      apply Fin.ext
      unfold face seg
      dsimp only [Function.comp_apply]
      split_ifs <;> omega
    rw [x.pull_congr z f1, y.pull_congr z f2]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  have f3 : seg 0 (m₁ + 1) (m₁ + m₂ + 1) (by omega) ∘ face m₁ (m₁ + 1) =
      seg 0 m₁ (m₁ + m₂ + 1) (by omega) := by
    funext k
    apply Fin.ext
    unfold face seg
    dsimp only [Function.comp_apply]
    split_ifs <;> omega
  have f4 : seg m₁ (m₂ + 1) (m₁ + m₂ + 1) (by omega) ∘ face m₂ 0 =
      seg (m₁ + 1) m₂ (m₁ + m₂ + 1) (by omega) := by
    funext k
    apply Fin.ext
    unfold face seg
    dsimp only [Function.comp_apply]
    split_ifs <;> omega
  rw [x.pull_congr z f3, y.pull_congr z f4]
  module

end CechCochain

/-! ### Total cochains -/

variable (U K W) in
/-- **Čech cochains of total degree `n`** of `K` on `W`: a cochain of bidegree `(p, m)` for every
`p + m = n`. -/
abbrev CechTotalCochain (n : ℤ) : Type u :=
  ∀ (p : ℤ) (m : ℕ), p + m = n → CechCochain U K W p m

namespace CechTotalCochain

open CechCochain

variable {n n' : ℤ}

/-- The Čech part of the total differential, landing in bidegree `(p, m)`: the Čech differential
of the component of bidegree `(p, m - 1)`, and `0` for `m = 0`. -/
def vert (c : CechTotalCochain U K W n) (p : ℤ) : (m : ℕ) → p + m = n + 1 → CechCochain U K W p m
  | 0, _ => 0
  | m + 1, h => (c p m (by push_cast at h; omega)).delta

/-- **The total differential** `D = d_K + (-1)^p δ` of total cochains. -/
def d (c : CechTotalCochain U K W n) (n' : ℤ) (hn : n + 1 = n') : CechTotalCochain U K W n' :=
  fun p m h ↦ horiz (p - 1) p (c (p - 1) m (by omega)) + (p.negOnePow : ℤ) • c.vert p m (by omega)

/-- `horiz` applied to the components of a total cochain at equal degrees `a = a'` agrees. -/
theorem horiz_congr (c : CechTotalCochain U K W n) {a a' : ℤ} (q : ℤ) (i : ℕ) (e : a = a')
    (h : a + i = n) (h' : a' + i = n) : horiz a q (c a i h) = horiz a' q (c a' i h') := by
  subst e
  rfl

/-- The product `δ (c^{a,i}) ⌣ y` agrees at equal degrees `a = a'`. -/
theorem aw_delta_congr_left (μ : SectionProduct K) (c : CechTotalCochain U K W n) {a a' b q : ℤ}
    {i j m : ℕ} (e : a = a') (h : a + i = n) (h' : a' + i = n) (hab : a + b = q)
    (hab' : a' + b = q) (hm : i + 1 + j = m) (y : CechCochain U K W b j) :
    aw μ hab hm (c a i h).delta y = aw μ hab' hm (c a' i h').delta y := by
  subst e
  rfl

/-- The product `x ⌣ δ (c'^{b,j})` agrees at equal degrees `b = b'`. -/
theorem aw_delta_congr_right (μ : SectionProduct K) (c' : CechTotalCochain U K W n')
    {a b b' q : ℤ} {i j m : ℕ} (e : b = b') (h : b + j = n') (h' : b' + j = n')
    (hab : a + b = q) (hab' : a + b' = q) (hm : i + (j + 1) = m) (x : CechCochain U K W a i) :
    aw μ hab hm x (c' b j h).delta = aw μ hab' hm x (c' b' j h').delta := by
  subst e
  rfl

variable (μ : SectionProduct K)

/-- The summand of bidegree `(i, j)` of the cup product in bidegree `(p, m)`. -/
def cupTerm (c : CechTotalCochain U K W n) (c' : CechTotalCochain U K W n') {p : ℤ} {m : ℕ}
    (hp : p + m = n + n') (i j : ℕ) : CechCochain U K W p m :=
  if hij : i + j = m then
    ((((i : ℤ) * (n' - j)).negOnePow : ℤ)) • aw μ (a := n - i) (b := n' - j) (by omega) hij
      (c (n - i) i (by omega)) (c' (n' - j) j (by omega))
  else 0

/-- **The cup product of total cochains**: in bidegree `(p, m)`,
`(c ⌣ c')^{p,m} = ∑_{i + j = m} (-1)^{i (n' - j)} c^{n-i, i} ⌣ c'^{n'-j, j}`, with the
Alexander–Whitney product of the components. -/
def cup (c : CechTotalCochain U K W n) (c' : CechTotalCochain U K W n') (N : ℤ)
    (hN : n + n' = N) : CechTotalCochain U K W N :=
  fun p m h ↦ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
    cupTerm μ c c' (p := p) (m := m) (by omega) ij.1 ij.2

/-- `(-1)^a = (-1)^b` when `a - b` is even. -/
theorem negOnePow_congr {a b : ℤ} (h : Even (a - b)) :
    ((a.negOnePow : ℤˣ) : ℤ) = b.negOnePow :=
  congrArg _ ((Int.negOnePow_eq_iff a b).2 h)

/-- `(-1)^a (-1)^b = (-1)^(a + b)` in `ℤ`. -/
theorem negOnePow_mul_negOnePow (a b : ℤ) :
    ((a.negOnePow : ℤˣ) : ℤ) * b.negOnePow = (a + b).negOnePow := by
  rw [Int.negOnePow_add, Units.val_mul]

section Leibniz

variable (c : CechTotalCochain U K W n) (c' : CechTotalCochain U K W n') {p : ℤ} {m : ℕ}

/-- The summands of `D (c ⌣ c')` containing `d_K c`. -/
def hA (hp : p + m = n + n' + 1) (i j : ℕ) : CechCochain U K W p m :=
  if hij : i + j = m then
    ((((i : ℤ) * (n' - j)).negOnePow : ℤ)) • aw μ (a := n + 1 - i) (b := n' - j) (by omega) hij
      (horiz (n - i) (n + 1 - i) (c (n - i) i (by omega))) (c' (n' - j) j (by omega))
  else 0

/-- The summands of `D (c ⌣ c')` containing `d_K c'`. -/
def hB (hp : p + m = n + n' + 1) (i j : ℕ) : CechCochain U K W p m :=
  if hij : i + j = m then
    ((((i : ℤ) * (n' - j)).negOnePow : ℤ) * ((n - i : ℤ).negOnePow : ℤ)) •
      aw μ (a := n - i) (b := n' + 1 - j) (by omega) hij
      (c (n - i) i (by omega)) (horiz (n' - j) (n' + 1 - j) (c' (n' - j) j (by omega)))
  else 0

/-- The summands of `D (c ⌣ c')` containing `δ c`. -/
def vA (hp : p + m = n + n' + 1) (i j : ℕ) : CechCochain U K W p m :=
  if hij : i + 1 + j = m then
    (((p.negOnePow : ℤˣ) : ℤ) * (((i : ℤ) * (n' - j)).negOnePow : ℤ)) •
      aw μ (a := n - i) (b := n' - j) (by omega) hij
      (c (n - i) i (by omega)).delta (c' (n' - j) j (by omega))
  else 0

/-- The summands of `D (c ⌣ c')` containing `δ c'`. -/
def vB (hp : p + m = n + n' + 1) (i j : ℕ) : CechCochain U K W p m :=
  if hij : i + (j + 1) = m then
    (((p.negOnePow : ℤˣ) : ℤ) * (((i : ℤ) * (n' - j)).negOnePow : ℤ) * ((-1 : ℤ) ^ i)) •
      aw μ (a := n - i) (b := n' - j) (by omega) hij
      (c (n - i) i (by omega)) (c' (n' - j) j (by omega)).delta
  else 0

/-- The summands of `D c ⌣ c'` containing `δ c`. -/
def vA' (hp : p + m = n + n' + 1) (i j : ℕ) : CechCochain U K W p m :=
  if hij : i + j = m then
    ((((i : ℤ) * (n' - j)).negOnePow : ℤ) * ((n + 1 - i : ℤ).negOnePow : ℤ)) •
      aw μ (a := n + 1 - i) (b := n' - j) (by omega) hij
      (c.vert (n + 1 - i) i (by omega)) (c' (n' - j) j (by omega))
  else 0

/-- The summands of `(-1)^n c ⌣ D c'` containing `δ c'`. -/
def vB' (hp : p + m = n + n' + 1) (i j : ℕ) : CechCochain U K W p m :=
  if hij : i + j = m then
    (((n.negOnePow : ℤˣ) : ℤ) * (((i : ℤ) * (n' + 1 - j)).negOnePow : ℤ) *
        ((n' + 1 - j : ℤ).negOnePow : ℤ)) •
      aw μ (a := n - i) (b := n' + 1 - j) (by omega) hij
      (c (n - i) i (by omega)) (c'.vert (n' + 1 - j) j (by omega))
  else 0

/-- The differential of `K` applied to a summand of the cup product is `hA + hB`. -/
theorem horiz_cupTerm (hp : p - 1 + m = n + n') (hp' : p + m = n + n' + 1) (i j : ℕ) :
    horiz (p - 1) p (cupTerm μ c c' hp i j) = hA μ c c' hp' i j + hB μ c c' hp' i j := by
  unfold cupTerm hA hB
  by_cases hij : i + j = m
  · rw [dite_eq_left hij, dite_eq_left hij, dite_eq_left hij, horiz_zsmul,
      horiz_aw μ _ (a' := n + 1 - i) (b' := n' + 1 - j) (by omega) (by omega) (by omega),
      smul_add, smul_smul]
  · rw [dite_eq_right hij, dite_eq_right hij, dite_eq_right hij, horiz_zero, add_zero]

/-- A summand of `D c ⌣ c'` is `hA + vA'`. -/
theorem cupTerm_d_left (hp : p + m = n + 1 + n') (hp' : p + m = n + n' + 1) (i j : ℕ) :
    cupTerm μ (c.d (n + 1) rfl) c' hp i j = hA μ c c' hp' i j + vA' μ c c' hp' i j := by
  unfold cupTerm hA vA'
  by_cases hij : i + j = m
  · rw [dite_eq_left hij, dite_eq_left hij, dite_eq_left hij]
    simp only [d]
    rw [aw_add_left, aw_zsmul_left, smul_add, smul_smul,
      c.horiz_congr (n + 1 - i) i (show n + 1 - i - 1 = n - i by ring)]
  · rw [dite_eq_right hij, dite_eq_right hij, dite_eq_right hij, add_zero]

/-- A summand of `(-1)^n c ⌣ D c'` is `hB + vB'`. -/
theorem cupTerm_d_right (hp : p + m = n + (n' + 1)) (hp' : p + m = n + n' + 1) (i j : ℕ) :
    ((n.negOnePow : ℤˣ) : ℤ) • cupTerm μ c (c'.d (n' + 1) rfl) hp i j =
      hB μ c c' hp' i j + vB' μ c c' hp' i j := by
  unfold cupTerm hB vB'
  by_cases hij : i + j = m
  · rw [dite_eq_left hij, dite_eq_left hij, dite_eq_left hij]
    simp only [d]
    rw [aw_add_right, aw_zsmul_right]
    simp only [smul_add, smul_smul, mul_assoc]
    rw [c'.horiz_congr (n' + 1 - j) j (show n' + 1 - j - 1 = n' - j by ring) (h' := by omega)]
    refine congrArg₂ (· + ·) (congrArg (· • _) ?_) rfl
    rw [negOnePow_mul_negOnePow, negOnePow_mul_negOnePow]
    exact negOnePow_congr ⟨i, by ring⟩
  · rw [dite_eq_right hij, dite_eq_right hij, dite_eq_right hij, add_zero, smul_zero]

/-- `(-1)^p` times the Čech differential of a summand of the cup product is `vA + vB`. -/
theorem delta_cupTerm {k : ℕ} (hp : p + k = n + n') (hp' : p + (k + 1) = n + n' + 1) (i j : ℕ) :
    ((p.negOnePow : ℤˣ) : ℤ) • (cupTerm μ c c' hp i j).delta =
      vA μ c c' hp' i j + vB μ c c' hp' i j := by
  unfold cupTerm vA vB
  by_cases hij : i + j = k
  · rw [dite_eq_left hij, dite_eq_left (show i + 1 + j = k + 1 by omega),
      dite_eq_left (show i + (j + 1) = k + 1 by omega), delta_zsmul, delta_aw, smul_add,
      smul_add, smul_smul, smul_smul, smul_smul, mul_assoc]
  · rw [dite_eq_right hij, dite_eq_right (show ¬ i + 1 + j = k + 1 by omega),
      dite_eq_right (show ¬ i + (j + 1) = k + 1 by omega), delta_zero, smul_zero, add_zero]

/-- The summand `vA'` with `i = 0` vanishes. -/
theorem vA'_zero (hp : p + m = n + n' + 1) (j : ℕ) : vA' μ c c' hp 0 j = 0 := by
  unfold vA'
  split_ifs
  · exact (congrArg _ (aw_zero_left μ _ _ _)).trans (smul_zero _)
  · rfl

/-- The summand `vA'` at `(i + 1, j)` is `vA` at `(i, j)`. -/
theorem vA'_succ (hp : p + m = n + n' + 1) (i j : ℕ) :
    vA' μ c c' hp (i + 1) j = vA μ c c' hp i j := by
  unfold vA' vA
  by_cases hij : i + 1 + j = m
  · rw [dite_eq_left hij, dite_eq_left hij]
    simp only [vert]
    rw [c.aw_delta_congr_left μ (show n + 1 - ((i + 1 : ℕ) : ℤ) = n - i by push_cast; ring)
      (h' := by omega) (hab' := by omega)]
    congr 1
    rw [negOnePow_mul_negOnePow, negOnePow_mul_negOnePow]
    refine negOnePow_congr ⟨0, ?_⟩
    have hp' : p = n + n' - i - j := by omega
    subst hp'
    push_cast
    ring
  · rw [dite_eq_right hij, dite_eq_right hij]

/-- The summand `vB'` with `j = 0` vanishes. -/
theorem vB'_zero (hp : p + m = n + n' + 1) (i : ℕ) : vB' μ c c' hp i 0 = 0 := by
  unfold vB'
  split_ifs
  · exact (congrArg _ (aw_zero_right μ _ _ _)).trans (smul_zero _)
  · rfl

/-- The summand `vB'` at `(i, j + 1)` is `vB` at `(i, j)`. -/
theorem vB'_succ (hp : p + m = n + n' + 1) (i j : ℕ) :
    vB' μ c c' hp i (j + 1) = vB μ c c' hp i j := by
  unfold vB' vB
  by_cases hij : i + (j + 1) = m
  · rw [dite_eq_left hij, dite_eq_left hij]
    simp only [vert]
    rw [c'.aw_delta_congr_right μ (show n' + 1 - ((j + 1 : ℕ) : ℤ) = n' - j by push_cast; ring)
      (h' := by omega) (hab' := by omega)]
    congr 1
    rw [← Int.coe_negOnePow_natCast, negOnePow_mul_negOnePow, negOnePow_mul_negOnePow,
      negOnePow_mul_negOnePow, negOnePow_mul_negOnePow]
    refine negOnePow_congr ⟨0, ?_⟩
    have hp' : p = n + n' - i - j := by omega
    subst hp'
    push_cast
    ring
  · rw [dite_eq_right hij, dite_eq_right hij]

/-- The Čech part of the total differential vanishes in Čech degree `0`. -/
theorem vert_zero (c : CechTotalCochain U K W n) (p : ℤ) (h : p + ((0 : ℕ) : ℤ) = n + 1) :
    c.vert p 0 h = 0 := rfl

/-- In Čech degree `m + 1`, the Čech part of the total differential is the Čech differential of
the component of bidegree `(p, m)`. -/
theorem vert_succ (c : CechTotalCochain U K W n) (p : ℤ) (m : ℕ)
    (h : p + ((m + 1 : ℕ) : ℤ) = n + 1) :
    c.vert p (m + 1) h = (c p m (by push_cast at h; omega)).delta := rfl

/-- The component of bidegree `(p, m)` of the total differential. -/
theorem d_apply (c : CechTotalCochain U K W n) (n' : ℤ) (hn : n + 1 = n') (p : ℤ) (m : ℕ)
    (h : p + m = n') : c.d n' hn p m h =
      horiz (p - 1) p (c (p - 1) m (by omega)) + (p.negOnePow : ℤ) • c.vert p m (by omega) := rfl

/-- The component of bidegree `(p, m)` of the cup product. -/
theorem cup_apply (c : CechTotalCochain U K W n) (c' : CechTotalCochain U K W n') (N : ℤ)
    (hN : n + n' = N) (p : ℤ) (m : ℕ) (h : p + m = N) :
    cup μ c c' N hN p m h =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, cupTerm μ c c' (by omega) ij.1 ij.2 := rfl

/-- **The Leibniz rule for the cup product of total Čech cochains**:
`D (c ⌣ c') = D c ⌣ c' + (-1)^n c ⌣ D c'` for `c` of total degree `n`. -/
theorem d_cup (c : CechTotalCochain U K W n) (c' : CechTotalCochain U K W n') (N N' : ℤ)
    (hN : n + n' = N) (hN' : N + 1 = N') (p : ℤ) (m : ℕ) (h : p + m = N') :
    (cup μ c c' N hN).d N' hN' p m h = cup μ (c.d (n + 1) rfl) c' N' (by omega) p m h +
      ((n.negOnePow : ℤˣ) : ℤ) • cup μ c (c'.d (n' + 1) rfl) N' (by omega) p m h := by
  subst hN hN'
  have hp : p + m = n + n' + 1 := h
  rw [d_apply, cup_apply, cup_apply, cup_apply, horiz_sum, Finset.smul_sum]
  simp only [horiz_cupTerm μ c c' _ hp, cupTerm_d_left μ c c' _ hp, cupTerm_d_right μ c c' _ hp,
    Finset.sum_add_distrib]
  suffices H : ((p.negOnePow : ℤˣ) : ℤ) • (cup μ c c' (n + n') rfl).vert p m (by omega) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, vA' μ c c' hp ij.1 ij.2 +
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, vB' μ c c' hp ij.1 ij.2 by
    rw [H]
    abel
  rcases m with _ | k
  · rw [vert_zero, smul_zero, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
      Finset.sum_singleton]
    exact (add_zero _).symm.trans (congrArg₂ (· + ·) (vA'_zero μ c c' hp 0).symm
      (vB'_zero μ c c' hp 0).symm)
  · rw [vert_succ, cup_apply, delta_sum, Finset.smul_sum]
    simp only [delta_cupTerm μ c c' _ hp, Finset.sum_add_distrib]
    rw [Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ', vA'_zero, vB'_zero, zero_add, zero_add]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun ij _ ↦ (vA'_succ μ c c' hp ij.1 ij.2).symm)
      (Finset.sum_congr rfl fun ij _ ↦ (vB'_succ μ c c' hp ij.1 ij.2).symm)

end Leibniz

end CechTotalCochain

/-! ### Sections of the sheafified Čech double complex -/

section Bridge

/-- The Čech cochain of sections underlying a section of a term of the Čech double complex. -/
def secCochain {p : ℤ} {m : ℕ} (a : Γ(((cechBicomplex U K).X p).X m, W)) :
    CechCochain U K W p m :=
  fun x ↦ ((cechBiπ K p m x).app W a).down

/-- A section of a term of the Čech double complex is determined by its Čech cochain. -/
theorem secCochain_injective {p : ℤ} {m : ℕ} :
    Function.Injective (secCochain (U := U) (K := K) (W := W) (p := p) (m := m)) :=
  fun a b h ↦ cechBi_sections_ext K p m W a b fun x ↦ ULift.ext (congrFun h x)

/-- Every Čech cochain comes from a section of the corresponding term of the double complex. -/
theorem secCochain_surjective {p : ℤ} {m : ℕ} :
    Function.Surjective (secCochain (U := U) (K := K) (W := W) (p := p) (m := m)) := by
  intro c
  obtain ⟨a, ha⟩ := cechBi_sections_exists (U := U) K p m W fun x ↦ ULift.up (c x)
  exact ⟨a, funext fun x ↦ congrArg ULift.down (ha x)⟩

/-- `secCochain` is additive. -/
theorem secCochain_add {p : ℤ} {m : ℕ} (a b : Γ(((cechBicomplex U K).X p).X m, W)) :
    secCochain (a + b) = secCochain a + secCochain b := by
  funext x
  exact congrArg ULift.down (map_add _ a b)

/-- `secCochain` commutes with multiplication by an integer. -/
theorem secCochain_zsmul {p : ℤ} {m : ℕ} (k : ℤ) (a : Γ(((cechBicomplex U K).X p).X m, W)) :
    secCochain (k • a) = k • secCochain a := by
  funext x
  exact congrArg ULift.down (map_zsmul _ k a)

/-- `secCochain` sends `0` to `0`. -/
theorem secCochain_zero {p : ℤ} {m : ℕ} :
    secCochain (0 : Γ(((cechBicomplex U K).X p).X m, W)) = 0 := by
  simpa using secCochain_zsmul (U := U) (K := K) (W := W) (p := p) (m := m) 0 0

/-- A finite sum of morphisms of `𝒪_V`-modules acts on sections as the sum of the actions. -/
theorem sum_app_apply {F G : V.Modules} {α : Type*} (s : Finset α) (f : α → (F ⟶ G))
    (A : V.Opens) (x : Γ(F, A)) : (∑ i ∈ s, f i).app A x = ∑ i ∈ s, (f i).app A x :=
  map_sum (AddMonoidHom.mk' (fun ψ : F ⟶ G ↦ ψ.app A x) fun a b ↦ by
    rw [Scheme.Modules.Hom.add_app]; rfl) f s

/-- `ULift.down` commutes with finite sums. -/
theorem ulift_down_sum {A : Type u} [AddCommGroup A] {α : Type*} (s : Finset α)
    (f : α → ULift.{u} A) : (∑ i ∈ s, f i).down = ∑ i ∈ s, (f i).down :=
  map_sum (AddEquiv.ulift (α := A)) f s

/-- The horizontal differential of the Čech double complex is the differential of `K` on
Čech cochains. -/
theorem secCochain_horiz (p p' : ℤ) {m : ℕ} (a : Γ(((cechBicomplex U K).X p).X m, W)) :
    secCochain ((((cechBicomplex U K).d p p').f m).app W a) =
      CechCochain.horiz p p' (secCochain a) := by
  funext x
  have h := congrArg (fun φ ↦ (φ.app W a).down) (cechBi_d_f_cechBiπ (U := U) K p p' m x)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  exact h

/-- The vertical differential of the Čech double complex is the Čech differential on Čech
cochains. -/
theorem secCochain_vert (p : ℤ) (m : ℕ) (a : Γ(((cechBicomplex U K).X p).X m, W)) :
    secCochain (((((cechBicomplex U K).X p).d m ((m + 1 : ℕ) : ℤ))).app W a) =
      (secCochain a).delta := by
  funext y
  have h := congrArg (fun φ ↦ (φ.app W a).down) (cechBi_X_d_cechBiπ (U := U) K p m y)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, sum_app_apply,
    zsmul_app_apply] at h
  refine h.trans ((ulift_down_sum _ _).trans ?_)
  exact (Finset.sum_congr rfl fun (x : Fin (m + 2)) _ ↦ congrArg (fun t ↦ ((-1 : ℤ) ^ (x : ℕ)) • t)
    ((secCochain a).pull_congr y (succAbove_eq_face x))).trans
    (Fin.sum_univ_eq_sum_range (fun i ↦ ((-1 : ℤ) ^ i) • (secCochain a).pull y (face m i)) (m + 2))

end Bridge

/-! ### The contracting homotopy on a member of the cover -/

namespace CechCochain

variable {p : ℤ} {m : ℕ}

/-- The restriction of the component of a cochain at a tuple `t` to an open `A` inside
`W ⊓ inter U t`. -/
def resTo (c : CechCochain U K W p m) (t : Fin (m + 1) → ι) {A : V.Opens}
    (h : A ≤ W ⊓ inter U t) : Γ(K.X p, A) :=
  (K.X p).presheaf.map (homOfLE h).op (c t)

/-- Restrictions of the components at equal tuples agree. -/
theorem resTo_congr (c : CechCochain U K W p m) {t t' : Fin (m + 1) → ι} (e : t = t')
    {A : V.Opens} (h : A ≤ W ⊓ inter U t) (h' : A ≤ W ⊓ inter U t') :
    c.resTo t h = c.resTo t' h' := by
  subst e
  rfl

/-- Restricting `resTo` from `A` to `B ≤ A` is `resTo` to `B`. -/
theorem map_resTo (c : CechCochain U K W p m) (t : Fin (m + 1) → ι) {A B : V.Opens}
    (h : A ≤ W ⊓ inter U t) (i : B ≤ A) :
    (K.X p).presheaf.map (homOfLE i).op (c.resTo t h) = c.resTo t (i.trans h) :=
  presheaf_map_map _ _ _ _

/-- The restriction to `W ⊓ inter U t` itself is the component at `t`. -/
theorem resTo_self (c : CechCochain U K W p m) (t : Fin (m + 1) → ι)
    (h : W ⊓ inter U t ≤ W ⊓ inter U t) : c.resTo t h = c t :=
  presheaf_map_id _ _

/-- For `W ≤ U α`, the intersection over `x` is contained in the intersection over the tuple
`α x₀ ⋯ x_{m'-1}`. -/
theorem le_inter_cons {α : ι} (hW : W ≤ U α) {m' : ℕ} (x : Fin m' → ι) :
    W ⊓ inter U x ≤ W ⊓ inter U (Fin.cons α x : Fin (m' + 1) → ι) :=
  le_inf inf_le_left (le_inter fun a ↦ Fin.cases (inf_le_left.trans hW)
    (fun b ↦ inf_le_right.trans (leOfHom (interπ U x b))) a)

variable {α : ι} (hW : W ≤ U α)

/-- **The contracting homotopy** of the Čech complex on an open `W ⊆ U α`:
`(k c)_{x₀ ⋯ x_m} = c_{α x₀ ⋯ x_m}`. -/
def contract (c : CechCochain U K W p (m + 1)) : CechCochain U K W p m :=
  fun x ↦ c.resTo (Fin.cons α x) (le_inter_cons hW x)

/-- The constant cochain of degree `0` given by the component of `c` at `α`. -/
def augAt (c : CechCochain U K W p 0) : CechCochain U K W p 0 :=
  fun _ ↦ c.resTo (fun _ ↦ α) (le_inf inf_le_left (le_inter fun _ ↦ inf_le_left.trans hW))

/-- The contracting homotopy commutes with multiplication by an integer. -/
theorem contract_zsmul (k : ℤ) (c : CechCochain U K W p (m + 1)) :
    contract hW (k • c) = k • contract hW c := by
  funext x
  exact map_zsmul _ _ _

/-- The differential of `K` commutes with the contracting homotopy. -/
theorem horiz_contract (p' : ℤ) (c : CechCochain U K W p (m + 1)) :
    horiz p p' (contract hW c) = contract hW (horiz p p' c) := by
  funext x
  exact app_presheaf_map _ _ _

/-- Omitting the first entry of `α y₀ ⋯ y_{m'}` gives `y`. -/
theorem cons_comp_face_zero {m' : ℕ} (y : Fin (m' + 1) → ι) :
    (Fin.cons α y : Fin (m' + 2) → ι) ∘ face m' 0 = y := by
  funext k
  simp only [Function.comp_apply]
  have : face m' 0 k = k.succ := Fin.ext (by unfold face; simp)
  rw [this, Fin.cons_succ]

/-- Omitting the entry `i + 1` of `α y` is prepending `α` to `y` with its entry `i` omitted. -/
theorem cons_comp_face_succ {m' : ℕ} (y : Fin (m' + 2) → ι) (i : ℕ) :
    (Fin.cons α y : Fin (m' + 3) → ι) ∘ face (m' + 1) (i + 1) =
      Fin.cons α (y ∘ face m' i) := by
  funext k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · have : face (m' + 1) (i + 1) 0 = 0 := Fin.ext (by unfold face; simp)
    simp only [Function.comp_apply, this, Fin.cons_zero]
  · have : face (m' + 1) (i + 1) k.succ = (face m' i k).succ := by
      apply Fin.ext
      unfold face
      simp only [Fin.val_succ]
      split_ifs <;> omega
    simp only [Function.comp_apply, this, Fin.cons_succ]

/-- Omitting the second entry of the pair `α y₀` gives the tuple `α`. -/
theorem cons_comp_face_one (y : Fin 1 → ι) :
    (Fin.cons α y : Fin 2 → ι) ∘ face 0 1 = fun _ ↦ α := by
  funext k
  have : face 0 1 k = 0 := Fin.ext (by unfold face; simp)
  simp only [Function.comp_apply, this, Fin.cons_zero]

/-- The contraction of `δ c` at `y` is the alternating sum of the restrictions of the components
of `c` at the faces of `α y`. -/
theorem contract_delta_apply {m' : ℕ} (c : CechCochain U K W p m') (y : Fin (m' + 1) → ι) :
    contract hW c.delta y = ∑ i ∈ Finset.range (m' + 2), ((-1 : ℤ) ^ i) •
      c.resTo ((Fin.cons α y : Fin (m' + 2) → ι) ∘ face m' i)
        ((le_inter_cons hW y).trans (inf_inter_le_comp _ _)) := by
  unfold contract resTo delta
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul]
  exact congrArg _ (presheaf_map_map _ _ _ _)

/-- **The homotopy identity** `δ k + k δ = 1` in positive degrees. -/
theorem delta_contract_add (c : CechCochain U K W p (m + 1)) :
    (contract hW c).delta + contract hW c.delta = c := by
  funext y
  have e1 : (contract hW c).delta y = ∑ i ∈ Finset.range (m + 2), ((-1 : ℤ) ^ i) •
      c.resTo (Fin.cons α (y ∘ face m i))
        ((inf_inter_le_comp y (face m i)).trans (le_inter_cons hW _)) :=
    Finset.sum_congr rfl fun i _ ↦ congrArg _ (map_resTo _ _ _ _)
  rw [Pi.add_apply, e1, contract_delta_apply, Finset.sum_range_succ' _ (m + 2)]
  have e3 : ∀ i ∈ Finset.range (m + 2), ((-1 : ℤ) ^ (i + 1)) •
      c.resTo ((Fin.cons α y : Fin (m + 3) → ι) ∘ face (m + 1) (i + 1))
        ((le_inter_cons hW y).trans (inf_inter_le_comp _ _)) =
      -(((-1 : ℤ) ^ i) • c.resTo (Fin.cons α (y ∘ face m i))
        ((inf_inter_le_comp y (face m i)).trans (le_inter_cons hW _))) := fun i _ ↦ by
    rw [c.resTo_congr (cons_comp_face_succ y i) _
      ((inf_inter_le_comp y (face m i)).trans (le_inter_cons hW _)), pow_succ, mul_neg_one,
      neg_smul]
  rw [Finset.sum_congr rfl e3, Finset.sum_neg_distrib,
    c.resTo_congr (cons_comp_face_zero y) _ le_rfl, resTo_self, pow_zero, one_smul]
  abel

/-- **The homotopy identity in degree `0`**: `k δ c = c - c_α`. -/
theorem contract_delta_zero (c : CechCochain U K W p 0) :
    contract hW c.delta = c - augAt hW c := by
  funext y
  rw [contract_delta_apply, Finset.sum_range_succ, Finset.sum_range_one,
    c.resTo_congr (cons_comp_face_zero y) _ le_rfl, resTo_self,
    c.resTo_congr (cons_comp_face_one y) _
      (le_inf inf_le_left (le_inter fun _ ↦ inf_le_left.trans hW)), pow_zero, one_smul, pow_one,
    neg_one_smul, Pi.sub_apply, ← sub_eq_add_neg]
  rfl

end CechCochain

namespace CechTotalCochain

variable {n : ℤ}

/-- A total cochain is a **cocycle** when its total differential vanishes. -/
def IsCocycle (c : CechTotalCochain U K W n) : Prop :=
  ∀ (p : ℤ) (m : ℕ) (h : p + m = n + 1), c.d (n + 1) rfl p m h = 0

/-- `(-1)^(p - 1) · (-(-1)^p) = 1`. -/
theorem negOnePow_sub_one_mul (p : ℤ) :
    (((p - 1).negOnePow : ℤˣ) : ℤ) * -((p.negOnePow : ℤˣ) : ℤ) = 1 := by
  rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one, Units.val_neg, neg_mul_neg,
    ← Units.val_mul, Int.units_mul_self, Units.val_one]

/-- `(-1)^p · (-1)^p = 1` in `ℤ`. -/
theorem negOnePow_mul_self' (p : ℤ) : ((p.negOnePow : ℤˣ) : ℤ) * (p.negOnePow : ℤˣ) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

variable {α : ι} (hW : W ≤ U α)

/-- **The contracting homotopy of total cochains** on an open `W ⊆ U α`:
`(h c)^{p, m} = (-1)^p k (c^{p, m+1})`. -/
def homotopy (c : CechTotalCochain U K W n) (n' : ℤ) (hn : n' + 1 = n) :
    CechTotalCochain U K W n' :=
  fun p m h ↦ ((p.negOnePow : ℤˣ) : ℤ) •
    CechCochain.contract hW (c p (m + 1) (by push_cast; omega))

/-- A cocycle on `W ⊆ U α` is the total differential of its contraction in bidegrees `(p, m)`
with `m > 0`. -/
theorem eq_d_homotopy_succ (c : CechTotalCochain U K W n) (hc : c.IsCocycle) (p : ℤ) (k : ℕ)
    (n' : ℤ) (hn : n' + 1 = n) (h : p + ((k + 1 : ℕ) : ℤ) = n) :
    c p (k + 1) h = (c.homotopy hW n' hn).d n hn p (k + 1) h := by
  have H := hc p (k + 2) (by push_cast at h ⊢; omega)
  rw [d_apply, vert_succ] at H
  rw [d_apply, vert_succ]
  simp only [homotopy]
  rw [CechCochain.horiz_zsmul, CechCochain.horiz_contract, eq_neg_of_add_eq_zero_left H,
    ← neg_smul, CechCochain.contract_zsmul, smul_smul, CechCochain.delta_zsmul, smul_smul,
    negOnePow_sub_one_mul, negOnePow_mul_self', one_smul, one_smul]
  exact (CechCochain.delta_contract_add hW _).symm.trans (add_comm _ _)

/-- A cocycle on `W ⊆ U α` is, in bidegree `(n, 0)`, the total differential of its contraction
plus the constant cochain of its component at `α`. -/
theorem eq_d_homotopy_zero (c : CechTotalCochain U K W n) (hc : c.IsCocycle)
    (n' : ℤ) (hn : n' + 1 = n) (h : n + ((0 : ℕ) : ℤ) = n) :
    c n 0 h = (c.homotopy hW n' hn).d n hn n 0 h +
      CechCochain.augAt hW (c n 0 h) := by
  have H := hc n 1 (by push_cast; ring)
  rw [d_apply, vert_succ] at H
  rw [d_apply, vert_zero, smul_zero, add_zero]
  simp only [homotopy]
  rw [CechCochain.horiz_zsmul, CechCochain.horiz_contract, eq_neg_of_add_eq_zero_left H,
    ← neg_smul, CechCochain.contract_zsmul, smul_smul, negOnePow_sub_one_mul, one_smul,
    CechCochain.contract_delta_zero, sub_add_cancel]

section CupCocycle

variable {n n' : ℤ} (μ : SectionProduct K)

/-- The cup product with a vanishing first factor vanishes. -/
theorem cup_eq_zero_of_left (c : CechTotalCochain U K W n) (c' : CechTotalCochain U K W n')
    (hc : ∀ p m h, c p m h = 0) (N : ℤ) (hN : n + n' = N) (p : ℤ) (m : ℕ) (h : p + m = N) :
    cup μ c c' N hN p m h = 0 := by
  rw [cup_apply]
  refine Finset.sum_eq_zero fun ij _ ↦ ?_
  unfold cupTerm
  split_ifs
  · rw [hc, CechCochain.aw_zero_left, smul_zero]
  · rfl

/-- The cup product with a vanishing second factor vanishes. -/
theorem cup_eq_zero_of_right (c : CechTotalCochain U K W n) (c' : CechTotalCochain U K W n')
    (hc' : ∀ p m h, c' p m h = 0) (N : ℤ) (hN : n + n' = N) (p : ℤ) (m : ℕ) (h : p + m = N) :
    cup μ c c' N hN p m h = 0 := by
  rw [cup_apply]
  refine Finset.sum_eq_zero fun ij _ ↦ ?_
  unfold cupTerm
  split_ifs
  · rw [hc', CechCochain.aw_zero_right, smul_zero]
  · rfl

/-- **The cup product of cocycles is a cocycle.** -/
theorem IsCocycle.cup {c : CechTotalCochain U K W n} {c' : CechTotalCochain U K W n'}
    (hc : c.IsCocycle) (hc' : c'.IsCocycle) (N : ℤ) (hN : n + n' = N) :
    (CechTotalCochain.cup μ c c' N hN).IsCocycle := by
  intro p m h
  rw [d_cup μ c c' N (N + 1) hN rfl p m h,
    cup_eq_zero_of_left μ _ c' (fun p m h ↦ hc p m h),
    cup_eq_zero_of_right μ c _ (fun p m h ↦ hc' p m h), smul_zero, add_zero]

/-- **The component of bidegree `(N, 0)` of a cup product** is the product of the components of
bidegrees `(n, 0)` and `(n', 0)`. -/
theorem cup_apply_zero (c : CechTotalCochain U K W n) (c' : CechTotalCochain U K W n') (N : ℤ)
    (hN : n + n' = N) (h : N + ((0 : ℕ) : ℤ) = N) (x : Fin 1 → ι) :
    cup μ c c' N hN N 0 h x =
      μ.mul n n' N hN _ (c n 0 (by simp) x) (c' n' 0 (by simp) x) := by
  rw [cup_apply, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  unfold cupTerm
  rw [dite_eq_left (show ((0, 0) : ℕ × ℕ).1 + ((0, 0) : ℕ × ℕ).2 = 0 from rfl), Pi.smul_apply]
  have hs : ((((((0, 0) : ℕ × ℕ).1 : ℕ) : ℤ) * (n' - (((0, 0) : ℕ × ℕ).2 : ℕ))).negOnePow : ℤ) =
      1 := by
    simp
  rw [hs, one_smul]
  have hseg : seg 0 0 0 (by omega) = id := funext fun k ↦ Fin.ext (by unfold seg; simp)
  have key : ∀ (a b : ℤ) (ea : a = n) (eb : b = n') (hab : a + b = N) (ha : a + ((0 : ℕ) : ℤ) = n)
      (hb : b + ((0 : ℕ) : ℤ) = n'),
      μ.mul a b N hab (W ⊓ inter U x) (c a 0 ha x) (c' b 0 hb x) =
        μ.mul n n' N hN _ (c n 0 (by simp) x) (c' n' 0 (by simp) x) := by
    intro a b ea eb _ _ _
    subst ea eb
    rfl
  refine Eq.trans ?_ (key (n - (((0, 0) : ℕ × ℕ).1 : ℕ)) (n' - (((0, 0) : ℕ × ℕ).2 : ℕ))
    (by simp) (by simp) (by simp; omega) (by simp) (by simp))
  change μ.mul _ _ N _ _ ((c _ 0 _).pull x (seg 0 0 0 _)) ((c' _ 0 _).pull x (seg 0 0 0 _)) = _
  rw [CechCochain.pull_congr _ x hseg, CechCochain.pull_congr _ x hseg, CechCochain.pull_id,
    CechCochain.pull_id]

/-- A total cochain viewed in an equal degree. -/
def cast (c : CechTotalCochain U K W n) (n' : ℤ) (e : n = n') : CechTotalCochain U K W n' :=
  fun p m h ↦ c p m (by omega)

/-- A cocycle viewed in an equal degree is a cocycle. -/
theorem IsCocycle.cast {c : CechTotalCochain U K W n} (hc : c.IsCocycle) (n' : ℤ) (e : n = n') :
    (c.cast n' e).IsCocycle := by
  intro p m h
  rcases m with _ | m
  · exact hc p 0 (by omega)
  · exact hc p (m + 1) (by omega)

/-- **The iterated cup product** `c₀ ⌣ c₁ ⌣ ⋯ ⌣ c_q` of total cochains of degree `1`. -/
def cupFin : (q : ℕ) → (Fin (q + 1) → CechTotalCochain U K W 1) →
    CechTotalCochain U K W ((q : ℤ) + 1)
  | 0, c => (c 0).cast _ (by simp)
  | q + 1, c => cup μ (cupFin q fun i ↦ c i.castSucc) (c (Fin.last _)) _ (by push_cast; ring)

/-- **The iterated cup product of cocycles is a cocycle.** -/
theorem isCocycle_cupFin : (q : ℕ) → (c : Fin (q + 1) → CechTotalCochain U K W 1) →
    (∀ i, (c i).IsCocycle) → (cupFin μ q c).IsCocycle
  | 0, _, hc => (hc 0).cast _ _
  | q + 1, _, hc => (isCocycle_cupFin q _ fun i ↦ hc i.castSucc).cup μ (hc _) _ _

/-- The component of bidegree `(q + 2, 0)` of an iterated cup product. -/
theorem cupFin_succ_apply_zero (q : ℕ) (c : Fin (q + 2) → CechTotalCochain U K W 1)
    (h : (((q + 1 : ℕ) : ℤ) + 1) + ((0 : ℕ) : ℤ) = ((q + 1 : ℕ) : ℤ) + 1) (x : Fin 1 → ι) :
    cupFin μ (q + 1) c (((q + 1 : ℕ) : ℤ) + 1) 0 h x =
      μ.mul ((q : ℤ) + 1) 1 (((q + 1 : ℕ) : ℤ) + 1) (by push_cast; ring) _
        (cupFin μ q (fun i ↦ c i.castSucc) ((q : ℤ) + 1) 0 (by simp) x)
        (c (Fin.last _) 1 0 (by simp) x) :=
  cup_apply_zero μ _ _ _ _ h x

/-- The iterated cup product of a single cochain is that cochain. -/
theorem cupFin_zero_apply (c : Fin 1 → CechTotalCochain U K W 1) (p : ℤ) (m : ℕ)
    (h : p + m = ((0 : ℕ) : ℤ) + 1) : cupFin μ 0 c p m h = c 0 p m (by simpa using h) := rfl

end CupCocycle

end CechTotalCochain

/-! ### Total sections of the sheafified Čech double complex -/

section TotalSections

open ComplexShape

variable {k : ℤ}

variable (U K W) in
/-- Families of sections over `W` of the terms of bidegree `(p, m)`, `p + m = k`, of the Čech
double complex. -/
abbrev SecFamily (k : ℤ) : Type u :=
  ∀ (p : ℤ) (m : ℕ), p + m = k → Γ(((cechBicomplex U K).X p).X m, W)

/-- The section of the total complex with components `A` in the bidegrees `(k - m, m)`,
`m ≤ L`. -/
def totSec (L : ℕ) (A : SecFamily U K W k) : Γ((cechTotal U K).X k, W) :=
  ∑ m ∈ Finset.range (L + 1),
    ((cechBicomplex U K).ιTotal (up ℤ) (k - m) m k (by dsimp; omega)).app W (A (k - m) m (by omega))

/-- The vertical part of the total differential of a family of sections. -/
def vSec (A : SecFamily U K W k) (p : ℤ) :
    (m : ℕ) → p + m = k + 1 → Γ(((cechBicomplex U K).X p).X m, W)
  | 0, _ => 0
  | m + 1, h => ((((cechBicomplex U K).X p).d m ((m + 1 : ℕ) : ℤ))).app W
      (A p m (by push_cast at h; omega))

/-- The total differential of a family of sections. -/
def dSec (A : SecFamily U K W k) : SecFamily U K W (k + 1) :=
  fun p m h ↦ (((cechBicomplex U K).d (p - 1) p).f m).app W (A (p - 1) m (by omega)) +
    ((p.negOnePow : ℤˣ) : ℤ) • vSec A p m h

/-- The Čech cochains of the total differential of a family of sections form the total
differential of the Čech cochains of the family. -/
theorem secCochain_dSec (A : SecFamily U K W k) (p : ℤ) (m : ℕ) (h : p + m = k + 1) :
    secCochain (dSec A p m h) =
      CechTotalCochain.d (fun p m h ↦ secCochain (A p m h)) (k + 1) rfl p m h := by
  rw [CechTotalCochain.d_apply]
  unfold dSec
  rw [secCochain_add, secCochain_horiz, secCochain_zsmul]
  rcases m with _ | m
  · rw [CechTotalCochain.vert_zero]
    exact congrArg (_ + ·) (congrArg (_ • ·) secCochain_zero)
  · rw [CechTotalCochain.vert_succ]
    exact congrArg (_ + ·) (congrArg (_ • ·) (secCochain_vert (U := U) p m _))

/-- Every section of a zero `𝒪_V`-module is `0`. -/
theorem section_eq_zero_of_isZero {F : V.Modules} (hF : IsZero F) {A : V.Opens} (x : Γ(F, A)) :
    x = 0 := by
  have h : (𝟙 F : F ⟶ F) = 0 := hF.eq_of_src _ _
  have := congrArg (fun φ : F ⟶ F ↦ φ.app A x) h
  simpa using this

/-- For `K` concentrated in degrees `≥ a`, the terms of the Čech double complex of bidegree
`(p, m)` with `p < a` are zero. -/
theorem isZero_cechBicomplex_X_X {a : ℤ} [K.IsStrictlyGE a] {p : ℤ} (hp : p < a) (m : ℤ) :
    IsZero (((cechBicomplex U K).X p).X m) :=
  (HomologicalComplex.eval _ _ m).map_isZero
    ((coveringComplexOpens V U ⋙ embeddingUpNat.extendFunctor V.Modules).map_isZero
      (K.isZero_of_isStrictlyGE a p hp))

/-- **The total differential on total sections.** -/
theorem d_totSec (L : ℕ) (A : SecFamily U K W k)
    (hA : ∀ (p : ℤ) (h : p + ((L + 1 : ℕ) : ℤ) = k), A p (L + 1) h = 0) :
    ((cechTotal U K).d k (k + 1)).app W (totSec L A) = totSec (L + 1) (dSec A) := by
  unfold totSec
  rw [map_sum]
  have e1 : ∀ m ∈ Finset.range (L + 1), ((cechTotal U K).d k (k + 1)).app W
      (((cechBicomplex U K).ιTotal (up ℤ) (k - m) m k (by dsimp; omega)).app W
        (A (k - m) m (by omega))) =
      ((cechBicomplex U K).ιTotal (up ℤ) (k + 1 - m) m (k + 1) (by dsimp; omega)).app W
        ((((cechBicomplex U K).d (k - m) (k + 1 - m)).f m).app W (A (k - m) m (by omega))) +
      ((k - m : ℤ).negOnePow : ℤ) • ((cechBicomplex U K).ιTotal (up ℤ) (k - m) ((m + 1 : ℕ) : ℤ)
        (k + 1) (by dsimp; omega)).app W
        (((((cechBicomplex U K).X (k - m)).d m ((m + 1 : ℕ) : ℤ))).app W
          (A (k - m) m (by omega))) := by
    intro m _
    have H := StacksDraft.TotalSingleRow.ιTotal_d_up_ℤ' (cechBicomplex U K) (k - m) (k + 1 - m)
      m ((m + 1 : ℕ) : ℤ) k (k + 1) (by ring) (by push_cast; ring) (by ring) rfl
    have H' := congrArg (fun φ ↦ φ.app W (A (k - m) m (by omega))) H
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.Hom.add_app, AddCommGrpCat.hom_add, AddMonoidHom.add_apply,
      Units.smul_def, zsmul_app_apply] at H'
    exact H'
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
  have e2 : ∀ m ∈ Finset.range (L + 1 + 1),
      ((cechBicomplex U K).ιTotal (up ℤ) (k + 1 - m) m (k + 1) (by dsimp; omega)).app W
        (dSec A (k + 1 - m) m (by omega)) =
      ((cechBicomplex U K).ιTotal (up ℤ) (k + 1 - m) m (k + 1) (by dsimp; omega)).app W
        ((((cechBicomplex U K).d (k + 1 - m - 1) (k + 1 - m)).f m).app W
          (A (k + 1 - m - 1) m (by omega))) +
      ((k + 1 - m : ℤ).negOnePow : ℤ) • ((cechBicomplex U K).ιTotal (up ℤ) (k + 1 - m) m (k + 1)
        (by dsimp; omega)).app W (vSec A (k + 1 - m) m (by omega)) := fun m _ ↦ by
    unfold dSec
    rw [map_add, map_zsmul]
  rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib, Finset.sum_range_succ _ (L + 1),
    Finset.sum_range_succ' (fun m ↦ ((k + 1 - m : ℤ).negOnePow : ℤ) • _) (L + 1)]
  have hcongr1 : ∀ (q a a' : ℤ) (m : ℕ) (e : a = a') (h : a + m = k) (h' : a' + m = k),
      (((cechBicomplex U K).d a q).f m).app W (A a m h) =
        (((cechBicomplex U K).d a' q).f m).app W (A a' m h') := by
    intro q a a' m e h h'
    subst e
    rfl
  have hcongr2 : ∀ (a a' : ℤ) (m : ℕ) (e : a = a') (h : a + m = k) (h' : a' + m = k)
      (h1 : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (a, ((m + 1 : ℕ) : ℤ)) = k + 1)
      (h1' : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (a', ((m + 1 : ℕ) : ℤ)) = k + 1),
      ((a.negOnePow : ℤˣ) : ℤ) • ((cechBicomplex U K).ιTotal (up ℤ) a ((m + 1 : ℕ) : ℤ)
        (k + 1) h1).app W (((((cechBicomplex U K).X a).d m ((m + 1 : ℕ) : ℤ))).app W (A a m h)) =
      ((a'.negOnePow : ℤˣ) : ℤ) • ((cechBicomplex U K).ιTotal (up ℤ) a' ((m + 1 : ℕ) : ℤ)
        (k + 1) h1').app W (((((cechBicomplex U K).X a').d m ((m + 1 : ℕ) : ℤ))).app W
          (A a' m h')) := by
    intro a a' m e h h' h1 h1'
    subst e
    rfl
  have hlast : ((cechBicomplex U K).ιTotal (up ℤ) (k + 1 - ((L + 1 : ℕ) : ℤ)) ((L + 1 : ℕ) : ℤ)
      (k + 1) (by dsimp; omega)).app W ((((cechBicomplex U K).d (k + 1 - ((L + 1 : ℕ) : ℤ) - 1)
        (k + 1 - ((L + 1 : ℕ) : ℤ))).f ((L + 1 : ℕ) : ℤ)).app W
          (A (k + 1 - ((L + 1 : ℕ) : ℤ) - 1) (L + 1) (by omega))) = 0 := by
    rw [hA _ (by omega), map_zero, map_zero]
  have hfirst : ((k + 1 - ((0 : ℕ) : ℤ) : ℤ).negOnePow : ℤ) • ((cechBicomplex U K).ιTotal (up ℤ)
      (k + 1 - ((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) (k + 1) (by dsimp; omega)).app W
        (vSec A (k + 1 - ((0 : ℕ) : ℤ)) 0 (by omega)) = 0 := by
    rw [show vSec A (k + 1 - ((0 : ℕ) : ℤ)) 0 _ = 0 from rfl, map_zero, smul_zero]
  rw [hlast, hfirst]
  simp only [add_zero]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun m _ ↦ congrArg _
    (hcongr1 _ _ _ m (by ring) _ _)) (Finset.sum_congr rfl fun m _ ↦ ?_)
  exact hcongr2 _ _ m (by push_cast; ring) _ _ _ _

end TotalSections

/-! ### Morphisms into the derived category from Čech cocycles -/

open ComplexShape

variable (U) in
/-- **A Čech cocycle of total degree `n` on a sheaf `M`**: morphisms
`g^{p, m} : M ⟶ Č^m(𝒰, K^p)` for `p + m = n` whose sections over every open form a cocycle of the
total complex. This generalises `MMP.DeRham.CechGluingData` (two components, degree `n + 1`) to
cocycles with components in every Čech degree, such as cup products. -/
structure CechCocycleData (K : CochainComplex V.Modules ℤ) (M : V.Modules) (n : ℤ) where
  /-- The components. -/
  g (p : ℤ) (m : ℕ) (h : p + m = n) : M ⟶ ((cechBicomplex U K).X p).X m
  /-- The sections form a cocycle. -/
  isCocycle (W : V.Opens) (s : Γ(M, W)) :
    CechTotalCochain.IsCocycle (fun p m h ↦ secCochain ((g p m h).app W s))

namespace CechCocycleData

variable {M : V.Modules} {n : ℤ} (D : CechCocycleData U K M n)

/-- The Čech cochain of sections of `D` at a section `s` of `M`. -/
def sec (W : V.Opens) (s : Γ(M, W)) : CechTotalCochain U K W n :=
  fun p m h ↦ secCochain ((D.g p m h).app W s)

/-- The morphism `M ⟶ Tot^n Č(𝒰, K)` with components the `g^{n-m, m}` for `m ≤ (n - a).toNat`;
when `K` is concentrated in degrees `≥ a` these are all of them. -/
def cocycle (a : ℤ) : M ⟶ (cechTotal U K).X n :=
  ∑ m ∈ Finset.range ((n - a).toNat + 1),
    D.g (n - m) m (by omega) ≫ (cechBicomplex U K).ιTotal (up ℤ) (n - m) m n (by dsimp; omega)

/-- On sections, `cocycle` sends `s` to the total section with components the sections of `g`
at `s`. -/
theorem cocycle_app (a : ℤ) (W : V.Opens) (s : Γ(M, W)) :
    (D.cocycle a).app W s = totSec ((n - a).toNat) (fun p m h ↦ (D.g p m h).app W s) := by
  unfold cocycle totSec
  rw [sum_app_apply]
  rfl

/-- The composite of `cocycle` with the differential of the total Čech complex is zero. -/
theorem cocycle_d (a : ℤ) [K.IsStrictlyGE a] :
    D.cocycle a ≫ (cechTotal U K).d n (n + 1) = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  change ((cechTotal U K).d n (n + 1)).app W ((D.cocycle a).app W s) = (0 : M ⟶ _).app W s
  rw [Scheme.Modules.Hom.zero_app, cocycle_app, d_totSec]
  · refine (Finset.sum_eq_zero fun m _ ↦ ?_).trans rfl
    have h0 : dSec (fun p m h ↦ (D.g p m h).app W s) (n + 1 - m) m (by omega) = 0 := by
      apply secCochain_injective (U := U)
      rw [secCochain_dSec, secCochain_zero]
      exact D.isCocycle W s _ _ _
    rw [h0, map_zero]
  · intro p h
    exact section_eq_zero_of_isZero (isZero_cechBicomplex_X_X (a := a) (by omega) _) _

/-- **The morphism of complexes `M[-n] ⟶ Tot Č(𝒰, K)`** given by the cocycle. -/
def cechMap (a : ℤ) [K.IsStrictlyGE a] :
    (HomologicalComplex.single V.Modules (up ℤ) n).obj M ⟶ cechTotal U K :=
  HomologicalComplex.mkHomFromSingle (D.cocycle a) fun k hk ↦ by
    obtain rfl : n + 1 = k := hk
    exact D.cocycle_d a

/-- The component of `cechMap` in degree `n` is `cocycle`. -/
theorem cechMap_f (a : ℤ) [K.IsStrictlyGE a] : (D.cechMap a).f n =
    (HomologicalComplex.singleObjXSelf (up ℤ) n M).hom ≫ D.cocycle a :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The morphism `M ⟶ ℋ^n(K)` induced on cohomology sheaves. -/
def homologyMap (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] : M ⟶ K.homology n :=
  haveI := quasiIso_toCechTotal hU K a
  (HomologicalComplex.singleObjHomologySelfIso (up ℤ) n M).inv ≫
    HomologicalComplex.homologyMap (D.cechMap a) n ≫
      inv (HomologicalComplex.homologyMap (toCechTotal U K) n)

/-- **The cohomology map is induced by the component on a member of the cover.** On an open
`W ⊆ U α`, `homologyMap` sends a section `s` of `M` to the class of any cycle `z` of `K^n` whose
restriction to `W ⊓ U α` is the component of bidegree `(n, 0)` of the cocycle at `α`. -/
theorem homologyMap_app_eq (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] (α : ι)
    {W : V.Opens} (hW : W ≤ U α) (s : Γ(M, W)) (z : Γ(K.cycles n, W))
    (hz : ((cechBiπ K n 0 (fun _ ↦ α)).app W ((D.g n 0 (by simp)).app W s)).down =
      (K.X n).presheaf.map (homOfLE (inf_le_left : W ⊓ inter U (fun _ : Fin 1 ↦ α) ≤ W)).op
        ((K.iCycles n).app W z)) :
    (D.homologyMap hU a).app W s = (K.homologyπ n).app W z := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by ring⟩
  have hLa : k + 1 - a ≤ (((k + 1 - a).toNat : ℕ) : ℤ) := Int.self_le_toNat _
  have hc : (D.sec W s).IsCocycle := D.isCocycle W s
  have hY : ∀ (p : ℤ) (m : ℕ) (h : p + m = k), ∃ y : Γ(((cechBicomplex U K).X p).X m, W),
      secCochain y = (D.sec W s).homotopy hW k rfl p m h :=
    fun p m h ↦ secCochain_surjective _
  choose Y hY using hY
  have hYs : (fun p m h ↦ secCochain (Y p m h)) = (D.sec W s).homotopy hW k rfl := by
    funext p m h
    exact hY p m h
  have hsucc : ∀ (p : ℤ) (m : ℕ) (h : p + ((m + 1 : ℕ) : ℤ) = k + 1),
      (D.g p (m + 1) h).app W s = dSec Y p (m + 1) h := by
    intro p m h
    apply secCochain_injective (U := U)
    rw [secCochain_dSec, hYs]
    exact CechTotalCochain.eq_d_homotopy_succ hW (D.sec W s) hc p m k rfl h
  set t := (K.iCycles (k + 1)).app W z
  have hzero : (D.g (k + 1) 0 (by simp)).app W s =
      (cechAugBi K (k + 1)).app W t + dSec Y (k + 1) 0 (by simp) := by
    apply secCochain_injective (U := U)
    rw [secCochain_add, secCochain_dSec, hYs]
    refine (CechTotalCochain.eq_d_homotopy_zero hW (D.sec W s) hc k rfl _).trans
      ((add_comm _ _).trans (congrArg (· + _) ?_))
    funext x
    have e1 : CechCochain.augAt hW (D.sec W s (k + 1) 0 (by simp)) x =
        (K.X (k + 1)).presheaf.map (homOfLE (inf_le_left : W ⊓ inter U x ≤ W)).op t :=
      (congrArg (fun r ↦ (K.X (k + 1)).presheaf.map
        (homOfLE (le_inf inf_le_left (le_inter fun _ ↦ inf_le_left.trans hW) :
          W ⊓ inter U x ≤ W ⊓ inter U (fun _ : Fin 1 ↦ α))).op r) hz).trans
        (presheaf_map_map _ _ _ _)
    have e2 : secCochain ((cechAugBi K (k + 1)).app W t) x =
        (K.X (k + 1)).presheaf.map (homOfLE (inf_le_left : W ⊓ inter U x ≤ W)).op t :=
      (congrArg (fun φ ↦ (φ.app W t).down) (cechAugBi_cechBiπ (U := U) K (k + 1) x)).trans
        (cechAug_π_app _ x W t)
    exact e1.trans e2.symm
  have hι0 : ∀ (F : SecFamily U K W (k + 1)) (p p' : ℤ) (e : p = p') (h : p + ((0 : ℕ) : ℤ) = k + 1)
      (h' : p' + ((0 : ℕ) : ℤ) = k + 1) (hι hι'),
      ((cechBicomplex U K).ιTotal (up ℤ) p ((0 : ℕ) : ℤ) (k + 1) hι).app W (F p 0 h) =
        ((cechBicomplex U K).ιTotal (up ℤ) p' ((0 : ℕ) : ℤ) (k + 1) hι').app W (F p' 0 h') := by
    intro F p p' e h h' hι hι'
    subst e
    rfl
  have hcore : (D.cocycle a).app W s = ((toCechTotal U K).f (k + 1)).app W t +
      ((cechTotal U K).d k (k + 1)).app W (totSec ((k + 1 - a).toNat) Y) := by
    rw [cocycle_app, d_totSec _ Y fun p h ↦ section_eq_zero_of_isZero
      (isZero_cechBicomplex_X_X (a := a) (by omega) _) _]
    unfold totSec
    rw [Finset.sum_range_succ _ ((k + 1 - a).toNat + 1),
      section_eq_zero_of_isZero (isZero_cechBicomplex_X_X (a := a) (by omega) _)
        (dSec Y (k + 1 - (((k + 1 - a).toNat + 1 : ℕ) : ℤ)) ((k + 1 - a).toNat + 1) _),
      map_zero, add_zero, Finset.sum_range_succ', Finset.sum_range_succ']
    rw [hι0 (fun p m h ↦ (D.g p m h).app W s) _ (k + 1) (by simp) _ (by simp) _ (by simp),
      hι0 (dSec Y) _ (k + 1) (by simp) _ (by simp) _ (by simp)]
    have e3 : ∀ m ∈ Finset.range (k + 1 - a).toNat,
        ((cechBicomplex U K).ιTotal (up ℤ) (k + 1 - ((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) (k + 1)
          (by dsimp; omega)).app W ((D.g (k + 1 - ((m + 1 : ℕ) : ℤ)) (m + 1) (by omega)).app W s) =
        ((cechBicomplex U K).ιTotal (up ℤ) (k + 1 - ((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) (k + 1)
          (by dsimp; omega)).app W (dSec Y (k + 1 - ((m + 1 : ℕ) : ℤ)) (m + 1) (by omega)) :=
      fun m _ ↦ congrArg _ (hsucc _ m _)
    rw [Finset.sum_congr rfl e3, hzero, map_add,
      show ((toCechTotal U K).f (k + 1)).app W t = ((cechBicomplex U K).ιTotal (up ℤ) (k + 1)
        ((0 : ℕ) : ℤ) (k + 1) (by dsimp; omega)).app W ((cechAugBi K (k + 1)).app W t) from rfl]
    abel
  have m1 : (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (k + 1) M).inv ≫
      HomologicalComplex.cyclesMap (D.cechMap a) (k + 1) ≫ (cechTotal U K).iCycles (k + 1) =
        D.cocycle a := by
    rw [HomologicalComplex.cyclesMap_i,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc, cechMap_f, Iso.inv_hom_id_assoc]
  have hH : IsIso (HomologicalComplex.homologyMap (toCechTotal U K) (k + 1)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 ((quasiIso_toCechTotal hU K a).quasiIsoAt _)
  have e1 : D.homologyMap hU a ≫ HomologicalComplex.homologyMap (toCechTotal U K) (k + 1) =
      (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (k + 1) M).inv ≫
        HomologicalComplex.cyclesMap (D.cechMap a) (k + 1) ≫
          (cechTotal U K).homologyπ (k + 1) := by
    simp only [homologyMap, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
      HomologicalComplex.homologyπ_naturality]
  set y := totSec ((k + 1 - a).toNat) Y
  have hw : (HomologicalComplex.cyclesMap (D.cechMap a) (k + 1)).app W
      ((HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (k + 1) M).inv.app W s) =
      (HomologicalComplex.cyclesMap (toCechTotal U K) (k + 1)).app W z +
        ((cechTotal U K).toCycles k (k + 1)).app W y := by
    apply app_injective_of_mono ((cechTotal U K).iCycles (k + 1)) W
    have h1 := congrArg (fun φ ↦ φ.app W s) m1
    have h2 := congrArg (fun φ ↦ φ.app W z)
      (HomologicalComplex.cyclesMap_i (toCechTotal U K) (k + 1))
    have h3 := congrArg (fun φ ↦ φ.app W y) ((cechTotal U K).toCycles_i k (k + 1))
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h1 h2 h3
    rw [map_add, h1, h2, h3, hcore]
  apply (ConcreteCategory.bijective_of_isIso
    ((HomologicalComplex.homologyMap (toCechTotal U K) (k + 1)).app W)).1
  have h1 := congrArg (fun φ ↦ φ.app W s) e1
  have h2 := congrArg (fun φ ↦ φ.app W z)
    (HomologicalComplex.homologyπ_naturality (toCechTotal U K) (k + 1))
  have h4 := congrArg (fun φ ↦ φ.app W y) ((cechTotal U K).toCycles_comp_homologyπ k (k + 1))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.zero_app] at h1 h2 h4
  rw [h1, h2, hw, map_add, h4]
  simp

section

variable [HasDerivedCategory.{u} V.Modules]

/-- **The morphism `M[-n] ⟶ K` in the derived category** given by the cocycle: the morphism of
complexes `M[-n] ⟶ Tot Č(𝒰, K)` followed by the inverse of the quasi-isomorphism
`K ⟶ Tot Č(𝒰, K)`. -/
def derivedMap (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] :
    (DerivedCategory.singleFunctor V.Modules n).obj M ⟶ DerivedCategory.Q.obj K :=
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ (toCechTotal U K)).2
    (quasiIso_toCechTotal hU K a)
  (DerivedCategory.singleFunctorIsoCompQ V.Modules n).hom.app M ≫
    DerivedCategory.Q.map (D.cechMap a) ≫ inv (DerivedCategory.Q.map (toCechTotal U K))

/-- **The cohomology in degree `n` of `derivedMap` is `homologyMap`**, up to the canonical
identifications. -/
theorem homologyFunctor_map_derivedMap (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] :
    (DerivedCategory.homologyFunctor V.Modules n).map (D.derivedMap hU a) =
      (homologySingleIso n M).hom ≫ D.homologyMap hU a ≫
        ((DerivedCategory.homologyFunctorFactors V.Modules n).app K).inv := by
  have hq := quasiIso_toCechTotal hU K a
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _ (toCechTotal U K)).2 hq
  have hH : IsIso (HomologicalComplex.homologyMap (toCechTotal U K) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 (hq.quasiIsoAt _)
  rw [← cancel_mono ((DerivedCategory.homologyFunctorFactors V.Modules n).app K).hom]
  simp only [derivedMap, homologySingleIso, homologyMap, Functor.map_comp, Category.assoc,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  congr 1
  have h1 : (DerivedCategory.homologyFunctor V.Modules n).map
      (inv (DerivedCategory.Q.map (toCechTotal U K))) ≫
        (DerivedCategory.homologyFunctorFactors V.Modules n).hom.app K =
      (DerivedCategory.homologyFunctorFactors V.Modules n).hom.app (cechTotal U K) ≫
        (inv (HomologicalComplex.homologyMap (toCechTotal U K) n) :
          (cechTotal U K).homology n ⟶ K.homology n) := by
    rw [Functor.map_inv]
    refine (IsIso.inv_comp_eq _).2 ?_
    erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc, IsIso.hom_inv_id,
      Category.comp_id]
  erw [h1, DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
  exact iso_comp_aux (C := V.Modules)
    ((DerivedCategory.homologyFunctorFactors V.Modules n).app
      ((CochainComplex.singleFunctor V.Modules n).obj M))
    (HomologicalComplex.singleObjHomologySelfIso (up ℤ) n M)
    (HomologicalComplex.homologyMap (D.cechMap a) n ≫
      inv (HomologicalComplex.homologyMap (toCechTotal U K) n))
    ((DerivedCategory.homologyFunctorFactors V.Modules n).app K)

end

end CechCocycleData

end MMP.DeRham
