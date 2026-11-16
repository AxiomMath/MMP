module

public import MMP.AlgebraicGeometry.DeRham.LogCartierSheafIso
public import MMP.AlgebraicGeometry.DeRham.LogFormsWedge
public import MMP.AlgebraicGeometry.Cohomology.Cech.GluingCocycles
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact

/-!
# The Deligne–Illusie decomposition

Let `k` be a perfect field of characteristic `p`, `V` a smooth proper `k`-scheme of dimension
`n < p`, `S` a simple normal crossing divisor with complement `U`, `K^•` the logarithmic forms
and `𝒦` the complex `F_*K^•` extended to `ℤ` (`MMP.DeRham.FrobeniusSplittingData`). Deligne and
Illusie show that a lifting of `(V, S)` over `W₂(k)` splits `𝒦` in the derived category:
`⨁_{q ≤ n} K^q[-q] ≅ 𝒦`. The maps `K^q[-q] ⟶ 𝒦` are given by Čech cocycles of total degree `q`
whose component of bidegree `(q, 0)` represents the inverse Cartier isomorphism; on cohomology
sheaves they induce `C⁻¹ : K^q ≅ ℋ^q(𝒦)`, and `ℋ^m(𝒦) = 0` outside `0 ≤ m ≤ n`.

This file proves the decomposition from such cocycles, constructs the cocycle in degree `0` from
the `p`-th power map, and develops the algebra of the degree-`q` cocycles: restriction and
multilinearity of the iterated cup product of Čech cochains, the antisymmetrised cup product
of the degree-`1` cocycles of local Frobenius splittings, and the factorisation of alternating
maps through wedges of logarithmic `1`-forms on the affine opens of `U`.

## Main definitions

* `MMP.DeRham.FrobeniusSplittingData.IsCartierCocycle`: a Čech cocycle representing the inverse
  Cartier map.
* `MMP.DeRham.FrobeniusSplittingData.zeroCocycle`: the cocycle of `c₀ : K⁰ ⟶ F_*K⁰`.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.cupCochain`: the antisymmetrised
  cup product of the cochains of logarithmic `1`-forms.
* `MMP.DeRham.FrobeniusSplittingData.wedgeFin`: wedges of logarithmic `1`-forms.
* `MMP.DeRham.IsLocalSectionRel`, `MMP.DeRham.IsLocalSectionRel.glue`: morphisms of sheaves of
  modules from locally defined relations.

## Main results

* `MMP.DeRham.FrobeniusSplittingData.nonempty_iso_of_isCartierCocycle`: **the decomposition**
  from Čech cocycles representing the inverse Cartier map.
* `MMP.DeRham.FrobeniusSplittingData.isIso_homologyMap_of_isCartierCocycle`: such a cocycle
  induces the inverse Cartier isomorphism.
* `MMP.DeRham.FrobeniusSplittingData.homologyπ_eq_of_cartierRep_of_local`,
  `MMP.DeRham.FrobeniusSplittingData.exists_d_eq_of_cartierRep_zero`: representatives of `C⁻¹ 0`
  are locally boundaries.
* `MMP.DeRham.FrobeniusSplittingData.isZero_K_of_lt`: no logarithmic forms above the dimension.
* `MMP.DeRham.FrobeniusSplittingData.isCartierCocycle_zeroCocycle`.
* `MMP.DeRham.FrobeniusSplittingData.sectionProduct_isLinear`,
  `MMP.DeRham.CechTotalCochain.cupFin_update_add`, `cupFin_update_smul`, `res_cupFin`.
* `MMP.DeRham.FrobeniusSplittingData.sum_map_alternatingMap_eq_zero`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], Thm 2.1, §4.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius
open KaehlerDifferential

universe u v

namespace MMP.DeRham

section Sections

variable {V : Scheme.{u}}

/-- Sections of a sheaf of modules which agree near every point agree. -/
theorem eq_of_locally_eq_sections {M : V.Modules} {W : V.Opens} (s t : Γ(M, W))
    (h : ∀ x ∈ W, ∃ (W' : V.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      M.presheaf.map (homOfLE hW').op s = M.presheaf.map (homOfLE hW').op t) : s = t := by
  choose W' hW' hx hst using h
  exact TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} _)
    (fun x : W ↦ W' x.1 x.2) W (fun x ↦ homOfLE (hW' x.1 x.2))
    (fun x hxW ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx x hxW⟩) s t
    fun x ↦ hst x.1 x.2

end Sections

/-! ### Restriction and scalar multiplication of Čech cochains -/

section CochainAlgebra

open Stacks.CategoryTheory.CechComplex (inter interMap)

variable {V : Scheme.{u}} {ι : Type u} {U : ι → V.Opens} {K : CochainComplex V.Modules ℤ}

/-- Two successive restrictions of a function are the restriction along the composite inclusion. -/
theorem ring_presheaf_map_map {A B C : V.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A)
    (r : Γ(V, A)) : V.presheaf.map g.op (V.presheaf.map f.op r) = V.presheaf.map k.op r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun t : C ⟶ A => V.presheaf.map t.op r) (Subsingleton.elim _ _)

namespace CechCochain

variable {W W' W'' : V.Opens} {p : ℤ} {m : ℕ}

/-- The restriction of a Čech cochain on `W` to an open `W' ⊆ W`. -/
def res (h : W' ≤ W) (c : CechCochain U K W p m) : CechCochain U K W' p m :=
  fun x ↦ (K.X p).presheaf.map (homOfLE (inf_le_inf_right _ h)).op (c x)

/-- The value of a restricted cochain is the restriction of the value. -/
theorem res_apply (h : W' ≤ W) (c : CechCochain U K W p m) (x : Fin (m + 1) → ι) :
    c.res h x = (K.X p).presheaf.map (homOfLE (inf_le_inf_right _ h)).op (c x) := rfl

/-- Restricting twice is restricting once, to the smaller open. -/
theorem res_res (h : W' ≤ W) (h' : W'' ≤ W') (c : CechCochain U K W p m) :
    (c.res h).res h' = c.res (h'.trans h) :=
  funext fun _ ↦ presheaf_map_map _ _ _ _

/-- Pulling back a restricted cochain is restricting the pulled-back cochain. -/
theorem res_pull (h : W' ≤ W) (c : CechCochain U K W p m) {m' : ℕ} (z : Fin m' → ι)
    (g : Fin (m + 1) → Fin m') :
    (c.res h).pull z g = (K.X p).presheaf.map (homOfLE (inf_le_inf_right _ h)).op (c.pull z g) :=
  have hle : W' ⊓ inter U z ≤ W ⊓ inter U (z ∘ g) :=
    (inf_le_inf_right _ h).trans (inf_inter_le_comp z g)
  (presheaf_map_map _ _ (homOfLE hle) _).trans (presheaf_map_map _ _ (homOfLE hle) _).symm

/-- Restriction of Čech cochains is additive. -/
theorem res_add (h : W' ≤ W) (c c' : CechCochain U K W p m) :
    (c + c').res h = c.res h + c'.res h :=
  funext fun _ ↦ map_add _ _ _

/-- Restriction of Čech cochains commutes with integer multiples. -/
theorem res_zsmul (h : W' ≤ W) (k : ℤ) (c : CechCochain U K W p m) :
    (k • c).res h = k • c.res h :=
  funext fun _ ↦ map_zsmul _ _ _

/-- The restriction of the zero cochain is zero. -/
theorem res_zero (h : W' ≤ W) : (0 : CechCochain U K W p m).res h = 0 :=
  funext fun _ ↦ map_zero _

/-- Restriction of Čech cochains commutes with finite sums. -/
theorem res_sum (h : W' ≤ W) {α : Type*} (s : Finset α) (c : α → CechCochain U K W p m) :
    (∑ a ∈ s, c a).res h = ∑ a ∈ s, (c a).res h := by
  funext x
  simp only [res, Finset.sum_apply]
  exact map_sum _ _ _

/-- Restriction of Čech cochains commutes with the Čech differential. -/
theorem res_delta (h : W' ≤ W) (c : CechCochain U K W p m) :
    (c.res h).delta = c.delta.res h := by
  funext z
  simp only [delta, res_pull, res_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (map_zsmul _ _ _).symm

/-- Restriction of Čech cochains commutes with the differential of `K`. -/
theorem res_horiz (h : W' ≤ W) (p' : ℤ) (c : CechCochain U K W p m) :
    horiz p p' (c.res h) = (horiz p p' c).res h :=
  funext fun x ↦ app_presheaf_map (K.d p p') (homOfLE _) (c x)

/-- Restriction of Čech cochains commutes with the Alexander–Whitney product. -/
theorem res_aw (μ : SectionProduct K) {a b c : ℤ} (hab : a + b = c) {m₁ m₂ : ℕ}
    (hm : m₁ + m₂ = m) (h : W' ≤ W) (x : CechCochain U K W a m₁) (y : CechCochain U K W b m₂) :
    aw μ hab hm (x.res h) (y.res h) = (aw μ hab hm x y).res h := by
  funext z
  simp only [aw, res_pull, res_apply]
  exact (μ.map_mul _ _ _ _ _ _ _).symm

/-- A Čech cochain multiplied by a function on `W`. -/
def smul (r : Γ(V, W)) (c : CechCochain U K W p m) : CechCochain U K W p m :=
  fun x ↦ V.presheaf.map (homOfLE (inf_le_left : W ⊓ inter U x ≤ W)).op r • c x

/-- The value of a cochain multiplied by `r` is the restriction of `r` times the value. -/
theorem smul_apply (r : Γ(V, W)) (c : CechCochain U K W p m) (x : Fin (m + 1) → ι) :
    c.smul r x = V.presheaf.map (homOfLE (inf_le_left : W ⊓ inter U x ≤ W)).op r • c x := rfl

/-- Pulling back a cochain multiplied by `r` multiplies the pulled-back cochain by the restriction
of `r`. -/
theorem smul_pull (r : Γ(V, W)) (c : CechCochain U K W p m) {m' : ℕ} (z : Fin m' → ι)
    (g : Fin (m + 1) → Fin m') :
    (c.smul r).pull z g =
      V.presheaf.map (homOfLE (inf_le_left : W ⊓ inter U z ≤ W)).op r • c.pull z g := by
  unfold pull smul
  rw [Scheme.Modules.map_smul, ring_presheaf_map_map]

/-- Multiplication of Čech cochains by a function is additive. -/
theorem smul_add (r : Γ(V, W)) (c c' : CechCochain U K W p m) :
    (c + c').smul r = c.smul r + c'.smul r :=
  funext fun _ ↦ _root_.smul_add _ _ _

/-- Multiplication of Čech cochains by a function commutes with integer multiples. -/
theorem smul_zsmul (r : Γ(V, W)) (k : ℤ) (c : CechCochain U K W p m) :
    (k • c).smul r = k • c.smul r := by
  funext x
  exact smul_comm (V.presheaf.map (homOfLE (inf_le_left : W ⊓ inter U x ≤ W)).op r) k (c x)

/-- Multiplication of Čech cochains by a function commutes with finite sums. -/
theorem smul_sum (r : Γ(V, W)) {α : Type*} (s : Finset α) (c : α → CechCochain U K W p m) :
    (∑ a ∈ s, c a).smul r = ∑ a ∈ s, (c a).smul r := by
  funext x
  simp only [smul, Finset.sum_apply]
  exact Finset.smul_sum

end CechCochain

/-- A product on sections is **linear** when it is linear over the functions in each variable. -/
structure SectionProduct.IsLinear (μ : SectionProduct K) : Prop where
  mul_smul_left (a b c : ℤ) (h : a + b = c) (A : V.Opens) (r : Γ(V, A)) (x : Γ(K.X a, A))
    (y : Γ(K.X b, A)) : μ.mul a b c h A (r • x) y = r • μ.mul a b c h A x y
  mul_smul_right (a b c : ℤ) (h : a + b = c) (A : V.Opens) (r : Γ(V, A)) (x : Γ(K.X a, A))
    (y : Γ(K.X b, A)) : μ.mul a b c h A x (r • y) = r • μ.mul a b c h A x y

namespace CechCochain

variable {W : V.Opens} {μ : SectionProduct K} {a b c : ℤ} {m₁ m₂ m : ℕ}

/-- For a linear product, the Alexander–Whitney product is linear over the functions in the first
factor. -/
theorem aw_smul_left (hμ : μ.IsLinear) (hab : a + b = c) (hm : m₁ + m₂ = m) (r : Γ(V, W))
    (x : CechCochain U K W a m₁) (y : CechCochain U K W b m₂) :
    aw μ hab hm (x.smul r) y = (aw μ hab hm x y).smul r := by
  funext z
  simp only [aw, smul_pull, smul_apply]
  exact hμ.mul_smul_left _ _ _ _ _ _ _ _

/-- For a linear product, the Alexander–Whitney product is linear over the functions in the second
factor. -/
theorem aw_smul_right (hμ : μ.IsLinear) (hab : a + b = c) (hm : m₁ + m₂ = m) (r : Γ(V, W))
    (x : CechCochain U K W a m₁) (y : CechCochain U K W b m₂) :
    aw μ hab hm x (y.smul r) = (aw μ hab hm x y).smul r := by
  funext z
  simp only [aw, smul_pull, smul_apply]
  exact hμ.mul_smul_right _ _ _ _ _ _ _ _

end CechCochain

namespace CechTotalCochain

open CechCochain

variable {W W' W'' : V.Opens} {n n' : ℤ}

/-- The restriction of a total Čech cochain on `W` to an open `W' ⊆ W`. -/
def res (h : W' ≤ W) (c : CechTotalCochain U K W n) : CechTotalCochain U K W' n :=
  fun p m hp ↦ (c p m hp).res h

/-- A total Čech cochain multiplied by a function on `W`. -/
def smul (r : Γ(V, W)) (c : CechTotalCochain U K W n) : CechTotalCochain U K W n :=
  fun p m hp ↦ (c p m hp).smul r

/-- Restriction of total Čech cochains commutes with the Čech component of the differential. -/
theorem res_vert (h : W' ≤ W) (c : CechTotalCochain U K W n) (p : ℤ) (m : ℕ)
    (hp : p + m = n + 1) : (c.res h).vert p m hp = (c.vert p m hp).res h := by
  rcases m with _ | m
  · exact (res_zero h).symm
  · exact res_delta h _

/-- Restriction of total Čech cochains commutes with the total differential. -/
theorem res_d (h : W' ≤ W) (c : CechTotalCochain U K W n) (n' : ℤ) (hn : n + 1 = n') :
    (c.res h).d n' hn = (c.d n' hn).res h := by
  funext p m hp
  change (c.res h).d n' hn p m hp = CechCochain.res h (c.d n' hn p m hp)
  rw [d_apply, d_apply, res_vert]
  change horiz (p - 1) p ((c (p - 1) m _).res h) + _ = _
  rw [res_horiz, CechCochain.res_add, CechCochain.res_zsmul]

/-- The restriction of a cocycle is a cocycle. -/
theorem IsCocycle.res {c : CechTotalCochain U K W n} (hc : c.IsCocycle) (h : W' ≤ W) :
    (c.res h).IsCocycle := by
  intro p m hp
  rw [res_d]
  change (c.d (n + 1) rfl p m hp).res h = 0
  rw [hc p m hp, CechCochain.res_zero]

/-- **Being a cocycle is local**: a total cochain whose restrictions to the members of an open
cover are cocycles is a cocycle. -/
theorem isCocycle_of_local (c : CechTotalCochain U K W n)
    (hloc : ∀ x ∈ W, ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧ (c.res h).IsCocycle) :
    c.IsCocycle := by
  intro p m hp
  funext z
  refine eq_of_locally_eq_sections _ _ fun y hy ↦ ?_
  obtain ⟨W', h, hyW', hc⟩ := hloc y hy.1
  refine ⟨W' ⊓ inter U z, inf_le_inf_right _ h, ⟨hyW', hy.2⟩, ?_⟩
  have := congrFun (hc p m hp) z
  rw [res_d] at this
  exact this.trans (map_zero _).symm

/-- Restriction of total Čech cochains commutes with the cup product. -/
theorem res_cup (μ : SectionProduct K) (h : W' ≤ W) (c : CechTotalCochain U K W n)
    (c' : CechTotalCochain U K W n') (N : ℤ) (hN : n + n' = N) :
    cup μ (c.res h) (c'.res h) N hN = (cup μ c c' N hN).res h := by
  funext p m hp
  change cup μ (c.res h) (c'.res h) N hN p m hp = CechCochain.res h (cup μ c c' N hN p m hp)
  rw [cup_apply, cup_apply]
  rw [CechCochain.res_sum]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  unfold cupTerm
  split_ifs
  · rw [CechCochain.res_zsmul]
    exact congrArg _ (res_aw μ _ _ h _ _)
  · exact (CechCochain.res_zero h).symm

/-- Restriction of total Čech cochains commutes with the iterated cup product. -/
theorem res_cupFin (μ : SectionProduct K) (h : W' ≤ W) :
    (q : ℕ) → (c : Fin (q + 1) → CechTotalCochain U K W 1) →
      cupFin μ q (fun i ↦ (c i).res h) = (cupFin μ q c).res h
  | 0, _ => rfl
  | q + 1, c => by
    change cup μ (cupFin μ q fun i ↦ (c i.castSucc).res h) ((c (Fin.last _)).res h) _ _ = _
    rw [res_cupFin μ h q, res_cup]
    rfl

section Multilinear

/-- The sum of two total Čech cochains. -/
def add (c c' : CechTotalCochain U K W n) : CechTotalCochain U K W n :=
  fun p m h ↦ c p m h + c' p m h

variable (μ : SectionProduct K)

/-- The cup product is additive in the first factor. -/
theorem cup_add_left (c₁ c₂ : CechTotalCochain U K W n) (c' : CechTotalCochain U K W n')
    (N : ℤ) (hN : n + n' = N) : cup μ (c₁.add c₂) c' N hN = (cup μ c₁ c' N hN).add (cup μ c₂ c' N hN) := by
  funext p m hp
  change cup μ (c₁.add c₂) c' N hN p m hp = cup μ c₁ c' N hN p m hp + cup μ c₂ c' N hN p m hp
  rw [cup_apply, cup_apply, cup_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  unfold cupTerm
  split_ifs
  · rw [← _root_.smul_add]
    exact congrArg _ (aw_add_left μ _ _ _ _ _)
  · exact (add_zero 0).symm

/-- The cup product is additive in the second factor. -/
theorem cup_add_right (c : CechTotalCochain U K W n) (c₁ c₂ : CechTotalCochain U K W n')
    (N : ℤ) (hN : n + n' = N) : cup μ c (c₁.add c₂) N hN = (cup μ c c₁ N hN).add (cup μ c c₂ N hN) := by
  funext p m hp
  change cup μ c (c₁.add c₂) N hN p m hp = cup μ c c₁ N hN p m hp + cup μ c c₂ N hN p m hp
  rw [cup_apply, cup_apply, cup_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  unfold cupTerm
  split_ifs
  · rw [← _root_.smul_add]
    exact congrArg _ (aw_add_right μ _ _ _ _ _)
  · exact (add_zero 0).symm

variable {μ}

/-- For a linear product, the cup product is linear over the functions in the first factor. -/
theorem cup_smul_left (hμ : μ.IsLinear) (r : Γ(V, W)) (c : CechTotalCochain U K W n)
    (c' : CechTotalCochain U K W n') (N : ℤ) (hN : n + n' = N) :
    cup μ (c.smul r) c' N hN = (cup μ c c' N hN).smul r := by
  funext p m hp
  change cup μ (c.smul r) c' N hN p m hp = CechCochain.smul r (cup μ c c' N hN p m hp)
  rw [cup_apply, cup_apply, CechCochain.smul_sum]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  unfold cupTerm
  split_ifs
  · rw [CechCochain.smul_zsmul]
    exact congrArg _ (aw_smul_left hμ _ _ _ _ _)
  · exact (funext fun _ ↦ (_root_.smul_zero _).symm)

/-- For a linear product, the cup product is linear over the functions in the second factor. -/
theorem cup_smul_right (hμ : μ.IsLinear) (r : Γ(V, W)) (c : CechTotalCochain U K W n)
    (c' : CechTotalCochain U K W n') (N : ℤ) (hN : n + n' = N) :
    cup μ c (c'.smul r) N hN = (cup μ c c' N hN).smul r := by
  funext p m hp
  change cup μ c (c'.smul r) N hN p m hp = CechCochain.smul r (cup μ c c' N hN p m hp)
  rw [cup_apply, cup_apply, CechCochain.smul_sum]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  unfold cupTerm
  split_ifs
  · rw [CechCochain.smul_zsmul]
    exact congrArg _ (aw_smul_right hμ _ _ _ _ _)
  · exact (funext fun _ ↦ (_root_.smul_zero _).symm)

variable (μ)

/-- **The iterated cup product is additive in each factor.** -/
theorem cupFin_update_add : (q : ℕ) → (c : Fin (q + 1) → CechTotalCochain U K W 1) →
    (i : Fin (q + 1)) → (x y : CechTotalCochain U K W 1) →
    cupFin μ q (Function.update c i (x.add y)) =
      (cupFin μ q (Function.update c i x)).add (cupFin μ q (Function.update c i y))
  | 0, c, i, x, y => by
    obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.1 i.2)
    simp only [cupFin, Function.update_self]
    rfl
  | q + 1, c, i, x, y => by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [cupFin, Function.update_self]
      have h : ∀ v, (fun k : Fin (q + 1) ↦ Function.update c (Fin.last (q + 1)) v k.castSucc) =
          fun k ↦ c k.castSucc := fun v ↦ funext fun k ↦
        Function.update_of_ne (Fin.castSucc_ne_last k) _ _
      rw [h, h, h, cup_add_right]
    · simp only [cupFin, Function.update_of_ne (Fin.castSucc_ne_last j).symm]
      have h : ∀ v, (fun k : Fin (q + 1) ↦ Function.update c j.castSucc v k.castSucc) =
          Function.update (fun k ↦ c k.castSucc) j v := fun v ↦
        (Function.update_comp_eq_of_injective c (Fin.castSucc_injective _) j v)
      rw [h, h, h, cupFin_update_add q _ j x y, cup_add_left]

variable {μ}

/-- **The iterated cup product is linear over the functions in each factor.** -/
theorem cupFin_update_smul (hμ : μ.IsLinear) (r : Γ(V, W)) :
    (q : ℕ) → (c : Fin (q + 1) → CechTotalCochain U K W 1) →
    (i : Fin (q + 1)) → (x : CechTotalCochain U K W 1) →
    cupFin μ q (Function.update c i (x.smul r)) = (cupFin μ q (Function.update c i x)).smul r
  | 0, c, i, x => by
    obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.1 i.2)
    simp only [cupFin, Function.update_self]
    rfl
  | q + 1, c, i, x => by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [cupFin, Function.update_self]
      have h : ∀ v, (fun k : Fin (q + 1) ↦ Function.update c (Fin.last (q + 1)) v k.castSucc) =
          fun k ↦ c k.castSucc := fun v ↦ funext fun k ↦
        Function.update_of_ne (Fin.castSucc_ne_last k) _ _
      rw [h, h, cup_smul_right hμ]
    · simp only [cupFin, Function.update_of_ne (Fin.castSucc_ne_last j).symm]
      have h : ∀ v, (fun k : Fin (q + 1) ↦ Function.update c j.castSucc v k.castSucc) =
          Function.update (fun k ↦ c k.castSucc) j v := fun v ↦
        (Function.update_comp_eq_of_injective c (Fin.castSucc_injective _) j v)
      rw [h, h, cupFin_update_smul hμ r q _ j x, cup_smul_left hμ]

end Multilinear

/-- The total differential of an integral linear combination of cochains is the combination of
their differentials. -/
theorem d_sum_zsmul {α : Type*} (s : Finset α) (a : α → ℤ) (c : α → CechTotalCochain U K W n)
    (n' : ℤ) (hn : n + 1 = n') :
    CechTotalCochain.d (fun p m h ↦ ∑ i ∈ s, a i • c i p m h) n' hn =
      fun p m h ↦ ∑ i ∈ s, a i • (c i).d n' hn p m h := by
  funext p m h
  simp only [d_apply]
  rcases m with _ | m
  · simp only [vert_zero, smul_zero, add_zero, horiz_sum, horiz_zsmul]
  · simp only [vert_succ, horiz_sum, horiz_zsmul, delta_sum, delta_zsmul, Finset.smul_sum,
      ← Finset.sum_add_distrib, _root_.smul_add, smul_comm ((p.negOnePow : ℤˣ) : ℤ) (a _)]

/-- An integral linear combination of cocycles is a cocycle. -/
theorem IsCocycle.sum_zsmul {α : Type*} (s : Finset α) (a : α → ℤ)
    {c : α → CechTotalCochain U K W n} (hc : ∀ i, (c i).IsCocycle) :
    CechTotalCochain.IsCocycle (fun p m h ↦ ∑ i ∈ s, a i • c i p m h) := by
  intro p m h
  rw [d_sum_zsmul]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [hc i p m h, smul_zero]

end CechTotalCochain

section SecCochain

variable {W W' : V.Opens}

/-- The Čech cochain of `r • a` is the Čech cochain of `a` multiplied by `r`. -/
theorem secCochain_smul {p : ℤ} {m : ℕ} (r : Γ(V, W)) (a : Γ(((cechBicomplex U K).X p).X m, W)) :
    secCochain (r • a) = (secCochain a).smul r := by
  funext x
  change ((cechBiπ K p m x).app W (r • a)).down = _
  rw [Scheme.Modules.Hom.app_smul]
  rfl

/-- The Čech cochain of the restriction of `a` is the restriction of the Čech cochain of `a`. -/
theorem secCochain_map {p : ℤ} {m : ℕ} (h : W' ≤ W) (a : Γ(((cechBicomplex U K).X p).X m, W)) :
    secCochain ((((cechBicomplex U K).X p).X m).presheaf.map (homOfLE h).op a) =
      (secCochain a).res h := by
  funext x
  change ((cechBiπ K p m x).app W' _).down = _
  rw [app_presheaf_map]
  rfl

end SecCochain

end CochainAlgebra

/-! ### Linearity of the wedge product -/

section FormsLinear

variable {k : Type u} [Field k] {V : Scheme.{u}} (f : V ⟶ Spec (.of k))

/-- On an affine open, the wedge product of forms is linear over the functions in the first
factor. -/
theorem formsWedge_smul_left_affine (i j m : ℕ) (h : i + j = m) (A : V.affineOpens)
    (r : Γ(V, A)) (ω : Γ(f.relativeDifferentialForms (i : ℤ), A))
    (η : Γ(f.relativeDifferentialForms (j : ℤ), A)) :
    formsWedge f i j m h A (r • ω) η = r • formsWedge f i j m h A ω η := by
  let := MMP.Mori.sectionAlgebra f A
  refine (formsAlgEquiv f m A).injective ?_
  rw [LinearEquiv.map_smul (formsAlgEquiv f m A)]
  apply Subtype.ext
  have h1 := coe_formsAlgEquiv_formsWedge f i j m h A (r • ω) η
  have h2 := coe_formsAlgEquiv_formsWedge f i j m h A ω η
  rw [Submodule.coe_smul, h1, h2, LinearEquiv.map_smul (formsAlgEquiv f i A),
    Submodule.coe_smul]
  exact smul_mul_assoc _ _ _

/-- On an affine open, the wedge product of forms is linear over the functions in the second
factor. -/
theorem formsWedge_smul_right_affine (i j m : ℕ) (h : i + j = m) (A : V.affineOpens)
    (r : Γ(V, A)) (ω : Γ(f.relativeDifferentialForms (i : ℤ), A))
    (η : Γ(f.relativeDifferentialForms (j : ℤ), A)) :
    formsWedge f i j m h A ω (r • η) = r • formsWedge f i j m h A ω η := by
  let := MMP.Mori.sectionAlgebra f A
  refine (formsAlgEquiv f m A).injective ?_
  rw [LinearEquiv.map_smul (formsAlgEquiv f m A)]
  apply Subtype.ext
  have h1 := coe_formsAlgEquiv_formsWedge f i j m h A ω (r • η)
  have h2 := coe_formsAlgEquiv_formsWedge f i j m h A ω η
  rw [Submodule.coe_smul, h1, h2, LinearEquiv.map_smul (formsAlgEquiv f j A),
    Submodule.coe_smul]
  exact mul_smul_comm _ _ _

/-- The wedge product of forms is linear over the functions in the first factor. -/
theorem formsWedge_smul_left (i j m : ℕ) (h : i + j = m) (B : V.Opens) (r : Γ(V, B))
    (ω : Γ(f.relativeDifferentialForms (i : ℤ), B))
    (η : Γ(f.relativeDifferentialForms (j : ℤ), B)) :
    formsWedge f i j m h B (r • ω) η = r • formsWedge f i j m h B ω η := by
  refine sub_eq_zero.1 (eq_zero_of_forall_affineOpens_le _ fun A hA ↦ ?_)
  rw [map_sub, formsWedge_map, Scheme.Modules.map_smul, Scheme.Modules.map_smul, formsWedge_map,
    formsWedge_smul_left_affine, sub_self]

/-- The wedge product of forms is linear over the functions in the second factor. -/
theorem formsWedge_smul_right (i j m : ℕ) (h : i + j = m) (B : V.Opens) (r : Γ(V, B))
    (ω : Γ(f.relativeDifferentialForms (i : ℤ), B))
    (η : Γ(f.relativeDifferentialForms (j : ℤ), B)) :
    formsWedge f i j m h B ω (r • η) = r • formsWedge f i j m h B ω η := by
  refine sub_eq_zero.1 (eq_zero_of_forall_affineOpens_le _ fun A hA ↦ ?_)
  rw [map_sub, formsWedge_map, Scheme.Modules.map_smul, Scheme.Modules.map_smul, formsWedge_map,
    formsWedge_smul_right_affine, sub_self]

end FormsLinear

/-- The Kähler differentials of the functions on an open, with the `k`-algebra structure of
`MMP.Mori.sectionAlgebra`. -/
abbrev sectionsKaehler {k : Type u} [Field k] {V : Scheme.{u}} (f : V ⟶ Spec (.of k))
    (A : V.Opens) : Type u :=
  letI := MMP.Mori.sectionAlgebra f A
  Ω[Γ(V, A)⁄k]

/-- The additive group of Kähler differentials of the functions on an open. -/
instance {k : Type u} [Field k] {V : Scheme.{u}} (f : V ⟶ Spec (.of k)) (A : V.Opens) :
    AddCommGroup (sectionsKaehler f A) :=
  letI := MMP.Mori.sectionAlgebra f A
  inferInstance

/-- The Kähler differentials of the functions on an open, as a module over those functions. -/
instance {k : Type u} [Field k] {V : Scheme.{u}} (f : V ⟶ Spec (.of k)) (A : V.Opens) :
    Module Γ(V, A) (sectionsKaehler f A) :=
  letI := MMP.Mori.sectionAlgebra f A
  inferInstance

/-- An additive map commutes with the sum of a list. -/
theorem list_sum_map_addMonoidHom {α X Y : Type*} [AddCommMonoid X] [AddCommMonoid Y]
    (g : X →+ Y) (w : α → X) (l : List α) : (l.map (fun a ↦ g (w a))).sum = g (l.map w).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- A linear map commutes with the sum of a list. -/
theorem linearMap_map_list_sum {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (g : M →ₗ[R] N) (l : List M) : g l.sum = (l.map g).sum :=
  map_list_sum g l

/-- An element of the first exterior power is the wedge of its image under
`exteriorPower.oneEquiv`. -/
theorem eq_ιMulti_oneEquiv {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (x : ⋀[R]^1 M) : x = exteriorPower.ιMulti R 1 (fun _ ↦ exteriorPower.oneEquiv R M x) :=
  (exteriorPower.oneEquiv R M).injective (by rw [exteriorPower.oneEquiv_ιMulti])

/-! ### Morphisms of sheaves of modules from local relations -/

section LocalRel

variable {V : Scheme.{u}} {M N : V.Modules} {A : V.Opens}

/-- A relation `R O s y` between sections of `M` and of `N` over the opens `O ⊆ A` **locally
defines a morphism** when every section has, near every point, a related section, related
sections agree wherever the sections agree, and the relation is stable under restriction, sums
and multiplication by functions. -/
structure IsLocalSectionRel (R : ∀ O : V.Opens, O ≤ A → Γ(M, O) → Γ(N, O) → Prop) : Prop where
  /-- Every section has, near every point, a related section. -/
  exists_local (O : V.Opens) (hO : O ≤ A) (s : Γ(M, O)) {x : V} (hx : x ∈ O) :
    ∃ (O' : V.Opens) (h : O' ≤ O), x ∈ O' ∧ ∃ y, R O' (h.trans hO) (M.presheaf.map (homOfLE h).op s) y
  /-- Sections related to sections agreeing on an open agree there. -/
  compat {O₁ O₂ O₃ : V.Opens} (h₁ : O₁ ≤ A) (h₂ : O₂ ≤ A) (h₃₁ : O₃ ≤ O₁) (h₃₂ : O₃ ≤ O₂)
    {s₁ y₁ s₂ y₂} : R O₁ h₁ s₁ y₁ → R O₂ h₂ s₂ y₂ →
    M.presheaf.map (homOfLE h₃₁).op s₁ = M.presheaf.map (homOfLE h₃₂).op s₂ →
    N.presheaf.map (homOfLE h₃₁).op y₁ = N.presheaf.map (homOfLE h₃₂).op y₂
  /-- The relation is stable under restriction. -/
  res {O O' : V.Opens} (hO : O ≤ A) (h : O' ≤ O) {s y} : R O hO s y →
    R O' (h.trans hO) (M.presheaf.map (homOfLE h).op s) (N.presheaf.map (homOfLE h).op y)
  /-- The relation is stable under sums. -/
  add {O : V.Opens} (hO : O ≤ A) {s y s' y'} : R O hO s y → R O hO s' y' →
    R O hO (s + s') (y + y')
  /-- The relation is stable under multiplication by functions. -/
  smul {O : V.Opens} (hO : O ≤ A) (r : Γ(V, O)) {s y} : R O hO s y → R O hO (r • s) (r • y)

namespace IsLocalSectionRel

variable {R : ∀ O : V.Opens, O ≤ A → Γ(M, O) → Γ(N, O) → Prop} (hR : IsLocalSectionRel R)

include hR

/-- Every section of `M` over an open inside `A` has a section of `N` restricting to every related
local section. -/
theorem exists_glue {O : V.Opens} (hO : O ≤ A) (s : Γ(M, O)) :
    ∃ t : Γ(N, O), ∀ (O' : V.Opens) (h : O' ≤ O) (y : Γ(N, O')),
      R O' (h.trans hO) (M.presheaf.map (homOfLE h).op s) y → N.presheaf.map (homOfLE h).op t = y := by
  choose O' hO' hx y hy using fun (x : O) ↦ hR.exists_local O hO s x.2
  have hcover : O ≤ iSup fun x : O ↦ O' x := fun x hx' ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩
  obtain ⟨t₀, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨N.val.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} _) (fun x : O ↦ O' x) O
    (fun x ↦ homOfLE (hO' x)) hcover y fun x x' ↦
      hR.compat _ _ inf_le_left inf_le_right (hy x) (hy x')
        ((presheaf_map_map _ _ (homOfLE ((inf_le_left : O' x ⊓ O' x' ≤ O' x).trans (hO' x))) s).trans
          (presheaf_map_map _ _ _ s).symm)
  let t : Γ(N, O) := t₀
  have ht' : ∀ x, N.presheaf.map (homOfLE (hO' x)).op t = y x := ht
  refine ⟨t, fun O₁ h₁ y₁ hy₁ ↦ eq_of_locally_eq_sections _ _ fun z hz ↦ ?_⟩
  have hzO : z ∈ O := h₁ hz
  refine ⟨O₁ ⊓ O' ⟨z, hzO⟩, inf_le_left, ⟨hz, hx ⟨z, hzO⟩⟩, ?_⟩
  rw [presheaf_map_map _ _ (homOfLE (inf_le_right.trans (hO' ⟨z, hzO⟩))),
    ← presheaf_map_map (homOfLE (hO' ⟨z, hzO⟩)) (homOfLE inf_le_right), ht']
  exact (hR.compat _ _ inf_le_right inf_le_left (hy ⟨z, hzO⟩) hy₁
    ((presheaf_map_map _ _ (homOfLE ((inf_le_left : O₁ ⊓ O' ⟨z, hzO⟩ ≤ O₁).trans h₁)) s).trans
      (presheaf_map_map _ _ _ s).symm))

/-- The section glued from the local related sections. -/
def glueSec {O : V.Opens} (hO : O ≤ A) (s : Γ(M, O)) : Γ(N, O) :=
  (hR.exists_glue hO s).choose

/-- The glued section restricts to every related local section. -/
theorem map_glueSec {O O' : V.Opens} (hO : O ≤ A) (h : O' ≤ O) (s : Γ(M, O)) (y : Γ(N, O'))
    (hy : R O' (h.trans hO) (M.presheaf.map (homOfLE h).op s) y) :
    N.presheaf.map (homOfLE h).op (hR.glueSec hO s) = y :=
  (hR.exists_glue hO s).choose_spec O' h y hy

/-- The glued section of `s` is any section related to `s`. -/
theorem glueSec_eq {O : V.Opens} (hO : O ≤ A) {s : Γ(M, O)} {y : Γ(N, O)} (hy : R O hO s y) :
    hR.glueSec hO s = y := by
  have := hR.map_glueSec hO le_rfl s y (by rwa [presheaf_map_id])
  rwa [presheaf_map_id] at this

/-- Gluing commutes with restriction. -/
theorem glueSec_res {O O' : V.Opens} (hO : O ≤ A) (h : O' ≤ O) (s : Γ(M, O)) :
    hR.glueSec (h.trans hO) (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (hR.glueSec hO s) := by
  refine eq_of_locally_eq_sections _ _ fun x hx ↦ ?_
  obtain ⟨O₁, h₁, hx₁, y, hy⟩ := hR.exists_local O' (h.trans hO) (M.presheaf.map (homOfLE h).op s) hx
  refine ⟨O₁, h₁, hx₁, ?_⟩
  rw [hR.map_glueSec _ h₁ _ y hy, presheaf_map_map _ _ (homOfLE (h₁.trans h))]
  refine (hR.map_glueSec hO (h₁.trans h) s y ?_).symm
  rwa [presheaf_map_map] at hy

/-- Gluing is additive. -/
theorem glueSec_add {O : V.Opens} (hO : O ≤ A) (s s' : Γ(M, O)) :
    hR.glueSec hO (s + s') = hR.glueSec hO s + hR.glueSec hO s' := by
  refine eq_of_locally_eq_sections _ _ fun x hx ↦ ?_
  obtain ⟨O₁, h₁, hx₁, y, hy⟩ := hR.exists_local O hO s hx
  obtain ⟨O₂, h₂, hx₂, y', hy'⟩ := hR.exists_local O₁ (h₁.trans hO)
    (M.presheaf.map (homOfLE h₁).op s') hx₁
  have hy₂ := hR.res _ h₂ hy
  rw [presheaf_map_map] at hy' hy₂
  refine ⟨O₂, h₂.trans h₁, hx₂, ?_⟩
  rw [map_add, hR.map_glueSec hO _ s _ hy₂, hR.map_glueSec hO _ s' _ hy']
  refine hR.map_glueSec hO _ _ _ ?_
  rw [map_add]
  exact hR.add _ hy₂ hy'

/-- Gluing is linear over the functions. -/
theorem glueSec_smul {O : V.Opens} (hO : O ≤ A) (r : Γ(V, O)) (s : Γ(M, O)) :
    hR.glueSec hO (r • s) = r • hR.glueSec hO s := by
  refine eq_of_locally_eq_sections _ _ fun x hx ↦ ?_
  obtain ⟨O₁, h₁, hx₁, y, hy⟩ := hR.exists_local O hO s hx
  refine ⟨O₁, h₁, hx₁, ?_⟩
  rw [Scheme.Modules.map_smul, hR.map_glueSec hO h₁ s y hy]
  refine hR.map_glueSec hO h₁ _ _ ?_
  rw [Scheme.Modules.map_smul]
  exact hR.smul _ _ hy

/-- **The morphism defined by a local relation**, on the sections over the opens inside `A`. -/
def glue (O : V.Opens) (hO : O ≤ A) : Γ(M, O) →+ Γ(N, O) :=
  AddMonoidHom.mk' (hR.glueSec hO) (hR.glueSec_add hO)

/-- The morphism defined by a local relation sends `s` to its glued section. -/
theorem glue_apply {O : V.Opens} (hO : O ≤ A) (s : Γ(M, O)) : hR.glue O hO s = hR.glueSec hO s :=
  rfl

end IsLocalSectionRel

end LocalRel

section FormsLinear2

variable {k : Type u} [Field k] {V : Scheme.{u}} (f : V ⟶ Spec (.of k))

/-- The algebraic form of the wedge of a form `a` of degree `i`, written as a wedge of `1`-forms,
with a `1`-form `b`. -/
theorem formsAlgEquiv_formsWedge_one_eq_ιMulti {i : ℕ} (G : V.affineOpens)
    (a : Γ(f.relativeDifferentialForms (i : ℤ), G))
    (b : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), G))
    (u : Fin i → sectionsKaehler f G)
    (ha : formsAlgEquiv f i G a = exteriorPower.ιMulti Γ(V, G) i u) :
    formsAlgEquiv f (i + 1) G (formsWedge f i 1 (i + 1) rfl G a b) =
      exteriorPower.ιMulti Γ(V, G) (i + 1)
        (Fin.snoc u (exteriorPower.oneEquiv Γ(V, G) (sectionsKaehler f G)
          (formsAlgEquiv f 1 G b))) := by
  let := MMP.Mori.sectionAlgebra f G
  apply Subtype.ext
  have h1 := coe_formsAlgEquiv_formsWedge f i 1 (i + 1) rfl G a b
  have h3 := congrArg Subtype.val (eq_ιMulti_oneEquiv (formsAlgEquiv f 1 G b))
  refine h1.trans ((congrArg₂ (· * ·) (congrArg Subtype.val ha) h3).trans ?_)
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · have : Fin.last i = Fin.natAdd i (0 : Fin 1) := Fin.ext (by simp)
    rw [Fin.snoc_last, this, Fin.append_right]
  · rw [Fin.snoc_castSucc]
    exact Fin.append_left _ _ j

end FormsLinear2

namespace FrobeniusSplittingData

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type v} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-! ### Logarithmic forms of degree above the dimension -/

/-- **There are no logarithmic forms of degree above the dimension.** -/
theorem isZero_K_of_lt {m : ℕ} (hm : n < m) : IsZero (D.K m) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology V) V.sheaf)
      (f.relativeDifferentials) n :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f n
  have h0 : ∀ (A : V.Opens) (ω : Γ(f.relativeDifferentialForms (m : ℤ), A)), ω = 0 :=
    fun A ω ↦ Stacks.SheafOfModules.TopWedge.exteriorPower_eq_zero_of_lt
      (_root_.SheafOfModules.algebras _ (f.relativeDifferentials)) n m hm (op A) ω
  rw [IsZero.iff_id_eq_zero]
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  exact D.he_inj m W ((h0 _ _).trans (h0 _ _).symm)

/-! ### Representatives of zero -/

/-- The inverse Cartier relation is additive in the representative. -/
theorem cartierRep_sub (q : ℕ) {W : V.Opens} {s s' z z' : Γ(D.K q, W)}
    (h : D.cartierRep q W s z) (h' : D.cartierRep q W s' z') :
    D.cartierRep q W (s - s') (z - z') := by
  intro A hA _
  let := MMP.Mori.sectionAlgebra f A
  simpa only [map_sub] using (h A hA).sub (h' A hA)

/-- The algebraic form of the differential of a logarithmic form is the de Rham differential of
its algebraic form. -/
theorem formsAlgEquiv_e_d (q : ℕ) {W : V.Opens} (hA : IsAffineOpen (W ⊓ D.U))
    (y : Γ(D.K q, W)) :
    letI := MMP.Mori.sectionAlgebra f (W ⊓ D.U)
    formsAlgEquiv f (q + 1) ⟨W ⊓ D.U, hA⟩ (D.e (q + 1) W ((D.d q).app W y)) =
      deRhamDifferential (A := k) q (formsAlgEquiv f q ⟨W ⊓ D.U, hA⟩ (D.e q W y)) := by
  let := MMP.Mori.sectionAlgebra f (W ⊓ D.U)
  rw [← formsAlgEquiv_d]
  exact congrArg (formsAlgEquiv f (q + 1) ⟨W ⊓ D.U, hA⟩) (D.he_d q W y)

/-- **A representative of `C⁻¹ 0` is locally a boundary**: a section `z` of `F_*K^{q+1}`
representing the inverse Cartier image of `0` is, near every point, the differential of a section
of `F_*K^q`. On a chart, its algebraic form is an exact logarithmic form, the differential of a
logarithmic form by the logarithmic Cartier theorem. -/
theorem exists_d_eq_of_cartierRep_zero (q : ℕ) {W : V.Opens} {z : Γ(D.K (q + 1), W)}
    (hz : D.cartierRep (q + 1) W 0 z) {x : V} (hx : x ∈ W) :
    ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧ ∃ y : Γ(D.K q, W'),
      (D.d q).app W' y = (D.K (q + 1)).presheaf.map (homOfLE h).op z := by
  obtain ⟨W₁, t, hle, hxW₁, hJ₁, -, hWU, hS⟩ :=
    exists_affineOpen_snc_chart_le f D.J D.hJ D.U D.hU hx
  refine ⟨W₁, hle, hxW₁, ?_⟩
  set z₁ : Γ(D.K (q + 1), W₁) := (D.K (q + 1)).presheaf.map (homOfLE hle).op z
  have hz₁ : D.cartierRep (q + 1) W₁ 0 z₁ := by
    simpa only [map_zero] using D.cartierRep_restrict (q + 1) hle hz
  have hA : IsAffineOpen ((W₁ : V.Opens) ⊓ D.U) := isAffineOpen_of_eq_basicOpen _ hWU
  suffices H : z₁ = 0 ∨ ∃ y : Γ(D.K q, W₁), (D.d q).app W₁ y = z₁ by
    rcases H with H | H
    · exact ⟨0, (map_zero _).trans H.symm⟩
    · exact H
  rcases subsingleton_or_nontrivial Γ(V, (W₁ : V.Opens) ⊓ D.U) with hL | hL
  · left
    let := MMP.Mori.sectionAlgebra f ((W₁ : V.Opens) ⊓ D.U)
    have : Subsingleton (⋀[Γ(V, (W₁ : V.Opens) ⊓ D.U)]^(q + 1)
        (Ω[Γ(V, (W₁ : V.Opens) ⊓ D.U)⁄k])) := Module.subsingleton Γ(V, (W₁ : V.Opens) ⊓ D.U) _
    refine D.he_inj (q + 1) W₁ ((formsAlgEquiv f (q + 1) ⟨_, hA⟩).injective ?_)
    exact Subsingleton.elim _ _
  have : CharP Γ(V, (W₁ : V.Opens) ⊓ D.U) p := D.charP_sections_of_nontrivial _
  let := MMP.Mori.sectionAlgebra f W₁
  let := MMP.Mori.sectionAlgebra f ((W₁ : V.Opens) ⊓ D.U)
  let : Algebra Γ(V, W₁) Γ(V, (W₁ : V.Opens) ⊓ D.U) :=
    (V.presheaf.map (homOfLE (inf_le_left : (W₁ : V.Opens) ⊓ D.U ≤ W₁)).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f
    (inf_le_left : (W₁ : V.Opens) ⊓ D.U ≤ W₁)
  have : IsLocalization.Away (∏ j, t j) Γ(V, (W₁ : V.Opens) ⊓ D.U) :=
    isLocalization_away_of_eq_basicOpen _ hWU inf_le_left
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : Algebra.Smooth k Γ(V, W₁) := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra f W₁.2
  let x' := formsAlgEquiv f (q + 1) ⟨_, hA⟩ (D.e (q + 1) W₁ z₁)
  have hlog := (D.mem_range_e_iff_mem_logForms (q + 1) W₁ t hJ₁ hWU hS (D.e (q + 1) W₁ z₁)).1
    ⟨z₁, rfl⟩
  have hrep0 : IsInvCartierRep p (q + 1) 0 x' := by
    simpa only [map_zero, presheaf_map_id] using hz₁ ⟨(W₁ : V.Opens) ⊓ D.U, hA⟩ le_rfl
  have hex := coe_mem_exactLogForms_of_isInvCartierRep_zero p
      (isUnit_algebraMap_of_isLocalization_away t)
      (forall_isMaximal_exists_isLocalLogCartier p t hS) x' hlog hrep0
  unfold exactLogForms at hex
  rw [Set.mem_ofPred_eq] at hex
  rcases hex with h0 | ⟨j, y', hj, hy', hdy⟩
  · left
    have hx0 : x' = 0 := Subtype.ext h0
    exact D.he_inj (q + 1) W₁ ((formsAlgEquiv f (q + 1) ⟨_, hA⟩).injective
      (hx0.trans (map_zero _).symm |>.trans (congrArg _ (map_zero _).symm)))
  · right
    obtain rfl : j = q := by omega
    obtain ⟨y, hy⟩ := (D.mem_range_e_iff_mem_logForms j W₁ t hJ₁ hWU hS
      ((formsAlgEquiv f j ⟨_, hA⟩).symm y')).2 (by rw [LinearEquiv.apply_symm_apply]; exact hy')
    refine ⟨y, D.he_inj (j + 1) W₁ ((formsAlgEquiv f (j + 1) ⟨_, hA⟩).injective ?_)⟩
    refine Subtype.ext (Eq.trans (congrArg Subtype.val ?_) hdy)
    refine (D.formsAlgEquiv_e_d j hA y).trans ?_
    rw [hy, LinearEquiv.apply_symm_apply]

/-- A representative of `C⁻¹ 0` in degree `0` vanishes. -/
theorem eq_zero_of_cartierRep_zero_zero {W : V.Opens} {z : Γ(D.K 0, W)}
    (hz : D.cartierRep 0 W 0 z) : z = 0 := by
  refine D.he_inj 0 W (Eq.trans ?_ (map_zero _).symm)
  refine D.eq_zero_of_forall_affineOpens 0 _ fun A hA hL ↦ ?_
  have : CharP Γ(V, A) p := D.charP_sections_of_nontrivial _
  let := MMP.Mori.sectionAlgebra f A
  have h := hz A hA
  simp only [map_zero] at h
  have h1 := IsInvCartierRep.eq_of_zero (p := p) (A := k) IsInvCartierRep.zero h
  have h2 := (formsAlgEquiv f 0 A).map_eq_zero_iff.1 h1.symm
  exact h2

/-- **Compatibility with all representatives from compatibility with some local ones.** If a
morphism `c : K^q ⟶ ℋ^q(F_*K^•)` sends, near every point, a logarithmic form to the class of some
representative of its inverse Cartier image, then it sends every logarithmic form to the class of
every representative: two representatives differ by a representative of `C⁻¹ 0`, which is locally
a boundary. -/
theorem homologyπ_eq_of_cartierRep_of_local (q : ℕ) (c : D.K q ⟶ D.complex.homology q)
    (hc : ∀ (W : V.Opens) (s : Γ(D.K q, W)) {x : V}, x ∈ W → ∃ (W' : V.Opens) (h : W' ≤ W),
      x ∈ W' ∧ ∃ z' : ToType ((D.complex.cycles q).val.obj (op W')),
        D.cartierRep q W' ((D.K q).presheaf.map (homOfLE h).op s)
          ((D.complex.iCycles q).val.app (op W') z') ∧
        c.val.app (op W') ((D.K q).presheaf.map (homOfLE h).op s) =
          (D.complex.homologyπ q).val.app (op W') z')
    {W : V.Opens} {s : Γ(D.K q, W)} {z : ToType ((D.complex.cycles q).val.obj (op W))}
    (hr : D.cartierRep q W s ((D.complex.iCycles q).val.app (op W) z)) :
    c.val.app (op W) s = (D.complex.homologyπ q).val.app (op W) z := by
  refine eq_of_locally_eq_sections (M := D.complex.homology q) _ _ fun x hx ↦ ?_
  obtain ⟨W', h, hxW', z', hz', hcz'⟩ := hc W s hx
  set z₁ : ToType ((D.complex.cycles q).val.obj (op W')) :=
    (D.complex.cycles q).val.map (homOfLE h).op z
  have hi₁ : (D.complex.iCycles q).val.app (op W') z₁ =
      (D.K q).presheaf.map (homOfLE h).op ((D.complex.iCycles q).val.app (op W) z) :=
    PresheafOfModules.naturality_apply (D.complex.iCycles q).val (homOfLE h).op z
  have hr₁ : D.cartierRep q W' ((D.K q).presheaf.map (homOfLE h).op s)
      ((D.complex.iCycles q).val.app (op W') z₁) := by
    rw [hi₁]
    exact D.cartierRep_restrict q h hr
  have h0 := D.cartierRep_sub q hr₁ hz'
  rw [sub_self] at h0
  have hcs : (D.complex.homology q).presheaf.map (homOfLE h).op (c.val.app (op W) s) =
      c.val.app (op W') ((D.K q).presheaf.map (homOfLE h).op s) :=
    (PresheafOfModules.naturality_apply c.val (homOfLE h).op s).symm
  have hπ : (D.complex.homology q).presheaf.map (homOfLE h).op
      ((D.complex.homologyπ q).val.app (op W) z) = (D.complex.homologyπ q).val.app (op W') z₁ :=
    (PresheafOfModules.naturality_apply (D.complex.homologyπ q).val (homOfLE h).op z).symm
  rcases q with _ | q
  · refine ⟨W', h, hxW', ?_⟩
    rw [hcs, hπ, hcz']
    rw [app_injective_of_mono (D.complex.iCycles 0) W'
      (sub_eq_zero.mp (D.eq_zero_of_cartierRep_zero_zero h0))]
  · obtain ⟨W'', h', hxW'', y, hy⟩ := D.exists_d_eq_of_cartierRep_zero q h0 hxW'
    refine ⟨W'', h'.trans h, hxW'', ?_⟩
    refine (presheaf_map_map (homOfLE h) (homOfLE h') _ _).symm.trans
      (Eq.trans ?_ (presheaf_map_map (homOfLE h) (homOfLE h') _ _))
    rw [hcs, hπ, hcz']
    set w : ToType ((D.complex.cycles (q + 1)).val.obj (op W'')) :=
      (D.complex.cycles (q + 1)).val.map (homOfLE h').op (z₁ - z')
    have hw : w = (D.complex.toCycles q (q + 1)).val.app (op W'') y := by
      apply app_injective_of_mono (D.complex.iCycles (q + 1)) W''
      have h1 : (D.complex.iCycles (q + 1)).val.app (op W'') w =
          (D.K (q + 1)).presheaf.map (homOfLE h').op
            ((D.complex.iCycles (q + 1)).val.app (op W') (z₁ - z')) :=
        PresheafOfModules.naturality_apply (D.complex.iCycles (q + 1)).val (homOfLE h').op _
      have hd : D.complex.d q (q + 1) = D.d q := CochainComplex.of_d
        (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q)) D.d q
      have h2 : (D.complex.iCycles (q + 1)).app W'' ((D.complex.toCycles q (q + 1)).app W'' y) =
          (D.d q).app W'' y := by
        have := congrArg (fun φ ↦ φ.app W'' y) (D.complex.toCycles_i q (q + 1))
        rwa [hd] at this
      change (D.complex.iCycles (q + 1)).val.app (op W'') w =
        (D.complex.iCycles (q + 1)).app W'' ((D.complex.toCycles q (q + 1)).app W'' y)
      rw [h2, h1, hy]
      exact congrArg _ (map_sub _ _ _)
    have h3 := congrArg (fun φ ↦ φ.app W'' y) (D.complex.toCycles_comp_homologyπ q (q + 1))
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h3
    have h4 : (D.complex.homologyπ (q + 1)).val.app (op W'') w = 0 := by
      rwa [hw]
    have h5 : (D.complex.homologyπ (q + 1)).val.app (op W'') w =
        (D.complex.homology (q + 1)).presheaf.map (homOfLE h').op
          ((D.complex.homologyπ (q + 1)).val.app (op W') z₁ -
            (D.complex.homologyπ (q + 1)).val.app (op W') z') := by
      rw [← map_sub]
      exact PresheafOfModules.naturality_apply (D.complex.homologyπ (q + 1)).val
        (homOfLE h').op _
    exact (sub_eq_zero.1 ((map_sub _ _ _).symm.trans (h5.symm.trans h4))).symm

/-! ### Čech cocycles representing the inverse Cartier map -/

section Cocycle

variable {κ : Type u} {U : κ → V.Opens}

/-- A Čech cocycle `Ψ` of total degree `q` on `K^q` with values in `F_*K^•` **represents the
inverse Cartier map** when, near every point of an open `W`, on some open `W' ⊆ W` inside a member
`U α` of the cover, its component of bidegree `(q, 0)` at `α` sends (the restriction of) a
logarithmic form `s` to (the restriction of) a representative of `C⁻¹ s`. -/
def IsCartierCocycle (q : ℕ) (Ψ : CechCocycleData U D.complexZ (D.K q) (q : ℤ)) : Prop :=
  ∀ (W : V.Opens) (s : Γ(D.K q, W)) (x : V), x ∈ W → ∃ (α : κ) (W' : V.Opens) (h : W' ≤ W)
    (_ : W' ≤ U α), x ∈ W' ∧ ∃ y : Γ(D.K q, W'),
    D.cartierRep q W' ((D.K q).presheaf.map (homOfLE h).op s) y ∧
    ((cechBiπ D.complexZ (q : ℤ) 0 (fun _ ↦ α)).app W'
        ((Ψ.g (q : ℤ) 0 (by simp)).app W' ((D.K q).presheaf.map (homOfLE h).op s))).down =
      (D.complexZ.X (q : ℤ)).presheaf.map
        (homOfLE (inf_le_left : W' ⊓ Stacks.CategoryTheory.CechComplex.inter U
          (fun _ : Fin 1 ↦ α) ≤ W')).op (D.toComplexZ q W' y)

/-- **The local description of the cohomology map of a Čech cocycle**, read in the cohomology of
`F_*K^•`: on an open `W ⊆ U α`, a section is sent to the class of any cycle `z` restricting to the
component of bidegree `(q, 0)` at `α`. -/
theorem homologyMap_comp_extendHomologyIso_app_eq (hU : ⨆ i, U i = ⊤) {q : ℕ}
    (Ψ : CechCocycleData U D.complexZ (D.K q) (q : ℤ)) (α : κ) {W : V.Opens} (hW : W ≤ U α)
    (s : Γ(D.K q, W)) (z : ToType ((D.complex.cycles q).val.obj (op W)))
    (hz : ((cechBiπ D.complexZ (q : ℤ) 0 (fun _ ↦ α)).app W ((Ψ.g (q : ℤ) 0 (by simp)).app W s)).down =
      (D.complexZ.X (q : ℤ)).presheaf.map
        (homOfLE (inf_le_left : W ⊓ Stacks.CategoryTheory.CechComplex.inter U
          (fun _ : Fin 1 ↦ α) ≤ W)).op (D.toComplexZ q W ((D.complex.iCycles q).val.app (op W) z))) :
    (Ψ.homologyMap hU 0 ≫ (D.complex.extendHomologyIso ComplexShape.embeddingUpNat
        (j := q) (j' := (q : ℤ)) rfl).hom).val.app (op W) s =
      (D.complex.homologyπ q).val.app (op W) z := by
  set e := ComplexShape.embeddingUpNat
  let z' := (D.complex.extendCyclesIso e (j := q) (j' := (q : ℤ)) rfl).inv.app W z
  have hz' : (D.complexZ.iCycles (q : ℤ)).app W z' =
      D.toComplexZ q W ((D.complex.iCycles q).val.app (op W) z) := by
    have h := congrArg (fun φ => φ.app W z)
      (D.complex.extendCyclesIso_inv_iCycles e (j := q) (j' := (q : ℤ)) rfl)
    exact h
  have h1 := Ψ.homologyMap_app_eq hU 0 α hW s z' (hz.trans (by rw [hz']))
  have h2 := congrArg (fun φ => φ.app W z')
    (D.complex.homologyπ_extendHomologyIso_hom e (j := q) (j' := (q : ℤ)) rfl)
  have h3 := congrArg (fun φ => φ.app W z)
    (D.complex.extendCyclesIso e (j := q) (j' := (q : ℤ)) rfl).inv_hom_id
  change (D.complex.extendHomologyIso e rfl).hom.app W ((Ψ.homologyMap hU 0).app W s) = _
  rw [h1]
  exact h2.trans (congrArg ((D.complex.homologyπ q).app W) h3)

/-- **A Čech cocycle representing the inverse Cartier map induces the inverse Cartier
isomorphism** `K^q ≅ ℋ^q(F_*K^•)` on cohomology sheaves. -/
theorem isIso_homologyMap_of_isCartierCocycle (hU : ⨆ i, U i = ⊤) {q : ℕ}
    (Ψ : CechCocycleData U D.complexZ (D.K q) (q : ℤ)) (hΨ : D.IsCartierCocycle q Ψ) :
    IsIso (Ψ.homologyMap hU 0) := by
  refine D.isIso_of_cartierRep q _ fun {W s z} hr ↦ ?_
  refine D.homologyπ_eq_of_cartierRep_of_local q _ (fun W s {x} hx ↦ ?_) hr
  obtain ⟨α, W', h, hα, hxW', y, hy, hgy⟩ := hΨ W s x hx
  refine ⟨W', h, hxW', ?_⟩
  obtain ⟨z', hz'⟩ := exists_iCycles_app_eq D.complex q W' y
    (D.cartierRep_complex_d_eq_zero hy)
  refine ⟨z', hz'.symm ▸ hy, ?_⟩
  exact D.homologyMap_comp_extendHomologyIso_app_eq hU Ψ α hα _ z'
    (hgy.trans (by erw [hz']))

end Cocycle

/-! ### Linearity of the wedge product of logarithmic forms -/

/-- The wedge product of logarithmic forms is linear over the functions in the first factor. -/
theorem wedge_smul_left (i j m : ℕ) (h : i + j = m) (A : V.Opens) (r : Γ(V, A))
    (s : Γ(D.K i, A)) (t : Γ(D.K j, A)) :
    D.wedge i j m h A (r • s) t = r • D.wedge i j m h A s t :=
  D.he_inj m A (by
    rw [D.e_wedge, D.he_smul, D.he_smul, D.e_wedge, formsWedge_smul_left])

/-- The wedge product of logarithmic forms is linear over the functions in the second factor. -/
theorem wedge_smul_right (i j m : ℕ) (h : i + j = m) (A : V.Opens) (r : Γ(V, A))
    (s : Γ(D.K i, A)) (t : Γ(D.K j, A)) :
    D.wedge i j m h A s (r • t) = r • D.wedge i j m h A s t :=
  D.he_inj m A (by
    rw [D.e_wedge, D.he_smul, D.he_smul, D.e_wedge, formsWedge_smul_right])

/-- The wedge product on `𝒦` is linear over the functions in the first factor. -/
theorem extendWedge_smul_left (i j m : ℕ) (h : i + j = m) {a b c : ℤ}
    (ha : ComplexShape.embeddingUpNat.f i = a) (hb : ComplexShape.embeddingUpNat.f j = b)
    (hc : ComplexShape.embeddingUpNat.f m = c) (A : V.Opens) (r : Γ(V, A))
    (x : Γ((D.complex.extend ComplexShape.embeddingUpNat).X a, A))
    (y : Γ((D.complex.extend ComplexShape.embeddingUpNat).X b, A)) :
    D.extendWedge i j m h ha hb hc A (r • x) y = r • D.extendWedge i j m h ha hb hc A x y := by
  rw [extendWedge_apply, extendWedge_apply, Scheme.Modules.Hom.app_smul, D.pushforward_smul]
  erw [D.wedge_smul_left]
  erw [← D.pushforward_smul, Scheme.Modules.Hom.app_smul]

/-- The wedge product on `𝒦` is linear over the functions in the second factor. -/
theorem extendWedge_smul_right (i j m : ℕ) (h : i + j = m) {a b c : ℤ}
    (ha : ComplexShape.embeddingUpNat.f i = a) (hb : ComplexShape.embeddingUpNat.f j = b)
    (hc : ComplexShape.embeddingUpNat.f m = c) (A : V.Opens) (r : Γ(V, A))
    (x : Γ((D.complex.extend ComplexShape.embeddingUpNat).X a, A))
    (y : Γ((D.complex.extend ComplexShape.embeddingUpNat).X b, A)) :
    D.extendWedge i j m h ha hb hc A x (r • y) = r • D.extendWedge i j m h ha hb hc A x y := by
  rw [extendWedge_apply, extendWedge_apply,
    Scheme.Modules.Hom.app_smul (D.complex.extendXIso _ hb).hom, D.pushforward_smul]
  erw [D.wedge_smul_right]
  erw [← D.pushforward_smul, Scheme.Modules.Hom.app_smul]

/-- **The wedge product on `𝒦` is linear** over the functions (which act on `F_*K^•` through
their `p`-th powers). -/
theorem sectionProduct_isLinear : D.sectionProduct.IsLinear where
  mul_smul_left a b c h A r x y := by
    by_cases hab : 0 ≤ a ∧ 0 ≤ b
    · simp only [sectionProduct, dite_eq_left hab]
      exact D.extendWedge_smul_left _ _ _ _ _ _ _ A r x y
    · simp only [sectionProduct, dite_eq_right hab, AddMonoidHom.zero_apply, smul_zero]
  mul_smul_right a b c h A r x y := by
    by_cases hab : 0 ≤ a ∧ 0 ≤ b
    · simp only [sectionProduct, dite_eq_left hab]
      exact D.extendWedge_smul_right _ _ _ _ _ _ _ A r x y
    · simp only [sectionProduct, dite_eq_right hab, AddMonoidHom.zero_apply, smul_zero]

/-! ### The antisymmetrised cup products of the local splittings -/

namespace LocalFrobeniusSplitting

open Stacks.CategoryTheory.CechComplex (inter)

variable {D} (L : D.LocalFrobeniusSplitting)

/-- The Čech cocycle of total degree `1` of the local splittings and their homotopies. -/
def oneCocycle : CechCocycleData L.U D.complexZ (D.K 1) ((0 : ℤ) + 1) :=
  L.toCechGluingSections.toCechGluingData.toCechCocycleData

/-- The total Čech cochain of degree `1` of a logarithmic `1`-form: the local splittings `φ α`
in bidegree `(1, 0)` and the homotopies `η α β` in bidegree `(0, 1)`. -/
def oneCochain (W : V.Opens) (ω : Γ(D.K 1, W)) : CechTotalCochain L.U D.complexZ W 1 :=
  (L.oneCocycle.sec W ω).cast 1 (zero_add 1)

/-- The total Čech cochain of a logarithmic `1`-form is a cocycle. -/
theorem isCocycle_oneCochain (W : V.Opens) (ω : Γ(D.K 1, W)) : (L.oneCochain W ω).IsCocycle :=
  (L.oneCocycle.isCocycle W ω).cast 1 _

/-- The total Čech cochain of a logarithmic `1`-form is additive in the form. -/
theorem oneCochain_add (W : V.Opens) (ω ω' : Γ(D.K 1, W)) :
    L.oneCochain W (ω + ω') = (L.oneCochain W ω).add (L.oneCochain W ω') := by
  funext p m h
  change secCochain ((L.oneCocycle.g p m _).app W (ω + ω')) = _
  rw [map_add, secCochain_add]
  rfl

/-- The total Čech cochain of a logarithmic `1`-form is linear over the functions. -/
theorem oneCochain_smul (W : V.Opens) (r : Γ(V, W)) (ω : Γ(D.K 1, W)) :
    L.oneCochain W (r • ω) = (L.oneCochain W ω).smul r := by
  funext p m h
  change secCochain ((L.oneCocycle.g p m _).app W (r • ω)) = _
  rw [Scheme.Modules.Hom.app_smul, secCochain_smul]
  rfl

/-- The total Čech cochain of a logarithmic `1`-form commutes with restriction. -/
theorem oneCochain_res {W W' : V.Opens} (h : W' ≤ W) (ω : Γ(D.K 1, W)) :
    L.oneCochain W' ((D.K 1).presheaf.map (homOfLE h).op ω) = (L.oneCochain W ω).res h := by
  funext p m hp
  change secCochain ((L.oneCocycle.g p m _).app W' _) = _
  rw [app_presheaf_map, secCochain_map]
  rfl

/-- **The antisymmetrised cup product** of the cochains of `q + 1` logarithmic `1`-forms:
`∑_σ sgn σ · c(ω_{σ 0}) ⌣ ⋯ ⌣ c(ω_{σ q})`. -/
def cupCochain (q : ℕ) (W : V.Opens) (θ : Fin (q + 1) → Γ(D.K 1, W)) :
    CechTotalCochain L.U D.complexZ W ((q : ℤ) + 1) :=
  fun p m h ↦ ∑ σ : Equiv.Perm (Fin (q + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    CechTotalCochain.cupFin D.sectionProduct q (fun i ↦ L.oneCochain W (θ (σ i))) p m h

/-- The antisymmetrised cup product of the cochains of logarithmic `1`-forms is a cocycle. -/
theorem isCocycle_cupCochain (q : ℕ) (W : V.Opens) (θ : Fin (q + 1) → Γ(D.K 1, W)) :
    (L.cupCochain q W θ).IsCocycle :=
  CechTotalCochain.IsCocycle.sum_zsmul _ _ fun _ ↦
    CechTotalCochain.isCocycle_cupFin _ q _ fun _ ↦ L.isCocycle_oneCochain W _

/-- The antisymmetrised cup product of the cochains of logarithmic `1`-forms commutes with
restriction. -/
theorem cupCochain_res (q : ℕ) {W W' : V.Opens} (h : W' ≤ W) (θ : Fin (q + 1) → Γ(D.K 1, W)) :
    L.cupCochain q W' (fun i ↦ (D.K 1).presheaf.map (homOfLE h).op (θ i)) =
      (L.cupCochain q W θ).res h := by
  funext p m hp
  change _ = CechCochain.res h (∑ σ : Equiv.Perm (Fin (q + 1)), _)
  rw [CechCochain.res_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [CechCochain.res_zsmul]
  congr 1
  simp only [L.oneCochain_res]
  exact congrFun (congrFun (congrFun (CechTotalCochain.res_cupFin _ h q _) p) m) hp

end LocalFrobeniusSplitting

/-! ### Wedges of logarithmic `1`-forms -/

/-- The wedge `θ₀ ∧ ⋯ ∧ θ_q` of `q + 1` logarithmic `1`-forms. -/
def wedgeFin {W : V.Opens} : (q : ℕ) → (Fin (q + 1) → Γ(D.K 1, W)) → Γ(D.K (q + 1), W)
  | 0, θ => θ 0
  | q + 1, θ => D.wedge (q + 1) 1 (q + 1 + 1) rfl W (wedgeFin q fun i ↦ θ i.castSucc)
      (θ (Fin.last _))

/-- The wedge of logarithmic `1`-forms commutes with restriction. -/
theorem wedgeFin_map {W W' : V.Opens} (h : W' ≤ W) : (q : ℕ) → (θ : Fin (q + 1) → Γ(D.K 1, W)) →
    (D.K (q + 1)).presheaf.map (homOfLE h).op (D.wedgeFin q θ) =
      D.wedgeFin q (fun i ↦ (D.K 1).presheaf.map (homOfLE h).op (θ i))
  | 0, _ => rfl
  | q + 1, θ => by
    change (D.K (q + 1 + 1)).presheaf.map (homOfLE h).op (D.wedge _ _ _ _ _ _ _) =
      D.wedge _ _ _ _ _ _ _
    rw [D.wedge_map, wedgeFin_map h q]

/-- The wedge of logarithmic `1`-forms is linear over the functions in the first factor. -/
theorem wedgeFin_update_zero_smul {W : V.Opens} (r : Γ(V, W)) : (q : ℕ) →
    (θ : Fin (q + 1) → Γ(D.K 1, W)) →
    D.wedgeFin q (Function.update θ 0 (r • θ 0)) = r • D.wedgeFin q θ
  | 0, θ => by
    change Function.update θ 0 (r • θ 0) 0 = r • θ 0
    rw [Function.update_self]
  | q + 1, θ => by
    change D.wedge _ _ _ _ _ (D.wedgeFin q fun i ↦ Function.update θ 0 (r • θ 0) i.castSucc)
      (Function.update θ 0 (r • θ 0) (Fin.last _)) = r • D.wedge _ _ _ _ _ _ _
    have h1 : (fun i : Fin (q + 1) ↦ Function.update θ 0 (r • θ 0) i.castSucc) =
        Function.update (fun i ↦ θ i.castSucc) 0 (r • θ 0) :=
      Function.update_comp_eq_of_injective θ (Fin.castSucc_injective _) 0 _
    rw [h1, Function.update_of_ne (Fin.last_pos.ne' : Fin.last (q + 1) ≠ 0)]
    have := wedgeFin_update_zero_smul r q (fun i ↦ θ i.castSucc)
    simp only [Fin.castSucc_zero] at this
    rw [this, D.wedge_smul_left]

/-- **The algebraic form of a wedge of logarithmic `1`-forms** on an affine open `G` of `O ∩ U`
is the product of the algebraic forms of the factors. -/
theorem formsAlgEquiv_map_e_wedgeFin {O : V.Opens} (G : V.affineOpens)
    (hG : (G : V.Opens) ≤ O ⊓ D.U) : (q : ℕ) → (θ : Fin (q + 1) → Γ(D.K 1, O)) →
    formsAlgEquiv f (q + 1) G ((f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
        (homOfLE hG).op (D.e (q + 1) O (D.wedgeFin q θ))) =
      exteriorPower.ιMulti Γ(V, G) (q + 1) (fun i ↦ exteriorPower.oneEquiv Γ(V, G)
        (sectionsKaehler f G)
        (formsAlgEquiv f 1 G ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
          (homOfLE hG).op (D.e 1 O (θ i)))))
  | 0, θ => by
    let := MMP.Mori.sectionAlgebra f G
    rw [wedgeFin]
    refine (eq_ιMulti_oneEquiv _).trans (congrArg _ (funext fun i ↦ ?_))
    rw [show i = 0 from Fin.ext (Nat.lt_one_iff.1 i.2)]
  | q + 1, θ => by
    let := MMP.Mori.sectionAlgebra f G
    rw [wedgeFin, D.e_wedge, formsWedge_map]
    have h2 := formsAlgEquiv_map_e_wedgeFin G hG q (fun i ↦ θ i.castSucc)
    have h4 := formsAlgEquiv_formsWedge_one_eq_ιMulti f G _
      ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hG).op
        (D.e 1 O (θ (Fin.last _)))) _ h2
    refine Eq.trans ?_ (h4.trans ?_)
    · congr 1
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc]

/-! ### Logarithmic forms on affine opens of the complement -/

/-- On an affine open `A ⊆ U`, restriction to `A` identifies the logarithmic `1`-forms over `A`
with the `1`-forms over `A`. -/
theorem exists_oneForm_linearMap (A : V.affineOpens) (hA : (A : V.Opens) ≤ D.U) :
    ∃ ρ : Γ(D.K 1, A) →ₗ[Γ(V, A)] Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), A),
      Function.Bijective ρ ∧ ∀ θ, ρ θ = (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (le_inf le_rfl hA : (A : V.Opens) ≤ (A : V.Opens) ⊓ D.U)).op (D.e 1 A θ) := by
  have hAU : (A : V.Opens) ≤ (A : V.Opens) ⊓ D.U := le_inf le_rfl hA
  let ρ : Γ(D.K 1, A) →ₗ[Γ(V, A)] Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), A) :=
    { toFun := fun θ ↦ (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE hAU).op (D.e 1 A θ)
      map_add' := fun θ θ' ↦ by simp only [map_add]
      map_smul' := fun r θ ↦ by
        rw [D.he_smul, Scheme.Modules.map_smul, ring_presheaf_map_map _ _ (𝟙 _), op_id,
          V.presheaf.map_id]
        rfl }
  have hinv : ∀ (q : ℤ) (ω : Γ(f.relativeDifferentialForms q, (A : V.Opens) ⊓ D.U)),
      (f.relativeDifferentialForms q).presheaf.map (homOfLE (inf_le_left : (A : V.Opens) ⊓ D.U ≤ A)).op
        ((f.relativeDifferentialForms q).presheaf.map (homOfLE hAU).op ω) = ω := fun q ω ↦
    (presheaf_map_map _ _ (𝟙 _) ω).trans (presheaf_map_id _ ω)
  refine ⟨ρ, ⟨fun θ θ' h ↦ ?_, fun ω₀ ↦ ?_⟩, fun θ ↦ rfl⟩
  · have h1 := congrArg (fun z ↦ (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
      (homOfLE (inf_le_left : (A : V.Opens) ⊓ D.U ≤ A)).op z) h
    simp only [ρ, LinearMap.coe_mk, AddHom.coe_mk, hinv] at h1
    exact D.he_inj 1 A h1
  · set ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), (A : V.Opens) ⊓ D.U) :=
      (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (inf_le_left : (A : V.Opens) ⊓ D.U ≤ A)).op ω₀
    obtain ⟨θ, hθ⟩ : ω ∈ Set.range (D.e 1 A) := by
      refine (D.he_range 1 A ω).2 fun W' hW' c _ ↦ ⟨⟨(∏ j, c j) •
        (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hW').op ω₀, ?_⟩,
        ⟨(∏ j, c j) • (f.relativeDifferentialForms ((1 + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hW').op
          (((f.deRhamComplex).d 1 (1 + 1)).val.app (op (A : V.Opens)) ω₀), ?_⟩⟩
      · rw [Scheme.Modules.map_smul, presheaf_map_map _ _ (homOfLE (inf_le_left.trans hW')),
          presheaf_map_map _ _ (homOfLE (inf_le_left.trans hW'))]
      · rw [Scheme.Modules.map_smul]
        congr 1
        have hnat := (PresheafOfModules.naturality_apply ((f.deRhamComplex).d 1 (1 + 1)).val
          (homOfLE (inf_le_left : (A : V.Opens) ⊓ D.U ≤ A)).op ω₀)
        exact (presheaf_map_map _ _ (homOfLE (inf_le_left.trans hW')) _).trans
          ((presheaf_map_map _ _ (homOfLE (inf_le_left.trans hW')) _).symm.trans
            (congrArg _ hnat.symm))
    refine ⟨θ, ?_⟩
    show (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hAU).op (D.e 1 A θ) = ω₀
    rw [hθ]
    exact (presheaf_map_map _ _ (𝟙 _) ω₀).trans (presheaf_map_id _ ω₀)

/-- On an affine open `A ⊆ U`, the logarithmic `1`-forms are the Kähler forms of `Γ(V, A)`, whose
exterior powers are the forms of higher degree: a family of wedges of logarithmic `1`-forms with
vanishing sum has vanishing sum in the exterior power. -/
theorem sum_map_ιMulti_eq_zero (q : ℕ) (A : V.affineOpens) (hA : (A : V.Opens) ≤ D.U)
    (l : List (Fin (q + 1) → Γ(D.K 1, A))) (hl : (l.map (D.wedgeFin q)).sum = 0) :
    (l.map (exteriorPower.ιMulti Γ(V, A) (q + 1))).sum = 0 := by
  have hAU : (A : V.Opens) ≤ (A : V.Opens) ⊓ D.U := le_inf le_rfl hA
  obtain ⟨ρ, hρ, hρapp⟩ := D.exists_oneForm_linearMap A hA
  let τ : Γ(D.K 1, A) →ₗ[Γ(V, A)] sectionsKaehler f A :=
    (exteriorPower.oneEquiv Γ(V, A) (sectionsKaehler f A)).toLinearMap ∘ₗ
      (formsAlgEquiv f 1 A).toLinearMap ∘ₗ ρ
  have hτ : Function.Bijective τ :=
    (exteriorPower.oneEquiv Γ(V, A) (sectionsKaehler f A)).bijective.comp
      ((formsAlgEquiv f 1 A).bijective.comp hρ)
  let τe := LinearEquiv.ofBijective τ hτ
  have hinj : Function.Injective (exteriorPower.map (q + 1) τ) := by
    intro x y hxy
    have h := congrArg (exteriorPower.map (q + 1) τe.symm.toLinearMap) hxy
    have hid : τe.symm.toLinearMap ∘ₗ τ = LinearMap.id :=
      LinearMap.ext fun θ ↦ τe.symm_apply_apply θ
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← exteriorPower.map_comp, hid,
      exteriorPower.map_id, LinearMap.id_apply, LinearMap.id_apply] at h
  obtain ⟨g, hg⟩ : ∃ g : Γ(D.K (q + 1), A) →+ ⋀[Γ(V, A)]^(q + 1) (sectionsKaehler f A),
      ∀ x, g x = formsAlgEquiv f (q + 1) A ((f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
        (homOfLE hAU).op (D.e (q + 1) A x)) :=
    ⟨AddMonoidHom.mk' (fun x ↦ formsAlgEquiv f (q + 1) A
      ((f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hAU).op
        (D.e (q + 1) A x))) (fun x y ↦ by simp only [map_add]), fun x ↦ rfl⟩
  have hE : ∀ θ : Fin (q + 1) → Γ(D.K 1, A),
      exteriorPower.map (q + 1) τ (exteriorPower.ιMulti Γ(V, A) (q + 1) θ) = g (D.wedgeFin q θ) := by
    intro θ
    refine (exteriorPower.map_apply_ιMulti τ θ).trans ?_
    rw [hg]
    refine Eq.trans ?_ (D.formsAlgEquiv_map_e_wedgeFin A hAU q θ).symm
    refine congrArg (exteriorPower.ιMulti Γ(V, A) (q + 1)) (funext fun i ↦ ?_)
    change exteriorPower.oneEquiv Γ(V, A) (sectionsKaehler f A) (formsAlgEquiv f 1 A (ρ (θ i))) = _
    rw [hρapp]
  have hsum : (l.map (fun θ ↦ g (D.wedgeFin q θ))).sum = 0 := by
    rw [list_sum_map_addMonoidHom g (D.wedgeFin q) l, hl, map_zero]
  have hs := linearMap_map_list_sum (exteriorPower.map (q + 1) τ)
    (l.map (exteriorPower.ιMulti Γ(V, A) (q + 1)))
  rw [List.map_map, show (exteriorPower.map (q + 1) τ ∘ exteriorPower.ιMulti Γ(V, A) (q + 1)) =
    fun θ ↦ g (D.wedgeFin q θ) from funext hE, hsum] at hs
  exact hinj (hs.trans (map_zero _).symm)

/-- **Alternating maps factor through wedges of logarithmic `1`-forms on the complement**: on an
affine open `A ⊆ U`, a `Γ(V, A)`-alternating map of `q + 1` logarithmic `1`-forms vanishes on
every family of wedges whose sum vanishes. -/
theorem sum_map_alternatingMap_eq_zero (q : ℕ) (A : V.affineOpens) (hA : (A : V.Opens) ≤ D.U)
    {N : Type*} [AddCommGroup N] [Module Γ(V, A) N]
    (F : Γ(D.K 1, A) [⋀^Fin (q + 1)]→ₗ[Γ(V, A)] N) (l : List (Fin (q + 1) → Γ(D.K 1, A)))
    (hl : (l.map (D.wedgeFin q)).sum = 0) : (l.map F).sum = 0 := by
  have hfun : (exteriorPower.alternatingMapLinearEquiv F) ∘
      exteriorPower.ιMulti Γ(V, A) (q + 1) = fun θ ↦ F θ :=
    funext fun θ ↦ exteriorPower.alternatingMapLinearEquiv_apply_ιMulti F θ
  have hG := linearMap_map_list_sum (exteriorPower.alternatingMapLinearEquiv F)
    (l.map (exteriorPower.ιMulti Γ(V, A) (q + 1)))
  rw [List.map_map, hfun, D.sum_map_ιMulti_eq_zero q A hA l hl, map_zero] at hG
  exact hG.symm

/-! ### The splitting in degree zero as a Čech cocycle -/

section DegreeZero

variable {κ : Type u} (U : κ → V.Opens)
  (c₀ : D.K 0 ⟶ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K 0))
  (hc₀ : ∀ (W : V.Opens) (s : Γ(D.K 0, W)), D.cartierRep 0 W s (c₀.app W s))

/-- The components of the Čech cocycle of `c₀ : K⁰ ⟶ F_*K⁰`: the augmentation of `c₀` in
bidegree `(0, 0)`, and `0` elsewhere. -/
def zeroCocycleComponent (p : ℤ) :
    (m : ℕ) → p + m = ((0 : ℕ) : ℤ) → (D.K 0 ⟶ ((cechBicomplex U D.complexZ).X p).X m)
  | 0, h => c₀ ≫ (D.complexZXIso 0).inv ≫
      (D.complexZ.XIsoOfEq (show ((0 : ℕ) : ℤ) = p by push_cast at h ⊢; omega)).hom ≫
        cechAugBi D.complexZ p
  | _ + 1, _ => 0

include hc₀ in
/-- The component of bidegree `(0, 0)` of the cocycle of `c₀` is killed by the differential of
`F_*K^•`. -/
theorem zeroCocycleComponent_comp_d_f (p p' : ℤ) (hp : p + ((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ))
    (hp' : p + 1 = p') :
    D.zeroCocycleComponent U c₀ p 0 hp ≫ ((cechBicomplex U D.complexZ).d p p').f ((0 : ℕ) : ℤ) =
      0 := by
  obtain rfl : p = 0 := by push_cast at hp; omega
  obtain rfl : p' = 1 := by omega
  have hn : cechAugBi (U := U) D.complexZ 0 ≫ ((cechBicomplex U D.complexZ).d 0 1).f ((0 : ℕ) : ℤ) =
      D.complexZ.d 0 1 ≫ cechAugBi D.complexZ 1 :=
    cechAugBi_naturality _ _ _
  simp only [zeroCocycleComponent]
  rw [Category.assoc, Category.assoc, Category.assoc, hn,
    HomologicalComplex.XIsoOfEq_hom_comp_d_assoc, ← Category.assoc c₀, ← Category.assoc (c₀ ≫ _),
    D.comp_complexZXIso_inv_d c₀ hc₀ 1 (by simp), Limits.zero_comp]

/-- The component of bidegree `(0, 0)` of the cocycle of `c₀` is killed by the Čech
differential. -/
theorem zeroCocycleComponent_comp_X_d (p : ℤ) (hp : p + ((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ)) :
    D.zeroCocycleComponent U c₀ p 0 hp ≫
      ((cechBicomplex U D.complexZ).X p).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) = 0 := by
  have h0 : cechAugBi (U := U) D.complexZ p ≫
      ((cechBicomplex U D.complexZ).X p).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) = 0 :=
    cechAugBi_comp_d D.complexZ p
  simp only [zeroCocycleComponent, Category.assoc, h0, Limits.comp_zero]

include hc₀ in
/-- The components of the cocycle of `c₀` form a total Čech cocycle on every section. -/
theorem isCocycle_zeroCocycleComponent (W : V.Opens) (s : Γ(D.K 0, W)) :
    CechTotalCochain.IsCocycle
      (fun p m h ↦ secCochain ((D.zeroCocycleComponent U c₀ p m h).app W s)) := by
  intro p m h
  rw [CechTotalCochain.d_apply]
  rcases m with _ | m
  · rw [CechTotalCochain.vert_zero, smul_zero, add_zero]
    change CechCochain.horiz (p - 1) p
      (secCochain ((D.zeroCocycleComponent U c₀ (p - 1) 0 (by push_cast at h ⊢; omega)).app W s))
      = 0
    rw [← secCochain_comp_d_f_app,
      D.zeroCocycleComponent_comp_d_f U c₀ hc₀ (p - 1) p _ (by ring),
      secCochain_zero_app]
  · rw [CechTotalCochain.vert_succ]
    change CechCochain.horiz (p - 1) p
      (secCochain ((D.zeroCocycleComponent U c₀ (p - 1) (m + 1) (by omega)).app W s)) +
      ((p.negOnePow : ℤˣ) : ℤ) •
        (secCochain ((D.zeroCocycleComponent U c₀ p m (by push_cast at h ⊢; omega)).app W s)).delta
      = 0
    rw [show D.zeroCocycleComponent U c₀ (p - 1) (m + 1) _ = 0 from rfl,
      secCochain_zero_app, CechCochain.horiz_zero, zero_add]
    rcases m with _ | m
    · rw [← secCochain_comp_X_d_app, D.zeroCocycleComponent_comp_X_d,
        secCochain_zero_app, smul_zero]
    · rw [show D.zeroCocycleComponent U c₀ p (m + 1) _ = 0 from rfl,
        secCochain_zero_app, CechCochain.delta_zero, smul_zero]

/-- **The splitting `ψ₀` as a Čech cocycle**: the augmentation of `c₀ : K⁰ ⟶ F_*K⁰`, of total
degree `0`. -/
def zeroCocycle : CechCocycleData U D.complexZ (D.K 0) ((0 : ℕ) : ℤ) where
  g := D.zeroCocycleComponent U c₀
  isCocycle := D.isCocycle_zeroCocycleComponent U c₀ hc₀

/-- The Čech cocycle of `c₀` represents the inverse Cartier map in degree `0`. -/
theorem isCartierCocycle_zeroCocycle (hU : ⨆ i, U i = ⊤) :
    D.IsCartierCocycle 0 (D.zeroCocycle U c₀ hc₀) := by
  intro W s x hx
  have hx' : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
  refine ⟨α, W ⊓ U α, inf_le_left, inf_le_right, ⟨hx, hα⟩, _, hc₀ _ _, ?_⟩
  set W' := W ⊓ U α
  set s' := (D.K 0).presheaf.map (homOfLE (inf_le_left : W' ≤ W)).op s
  change ((cechBiπ D.complexZ ((0 : ℕ) : ℤ) 0 (fun _ ↦ α)).app W'
    ((c₀ ≫ (D.complexZXIso 0).inv ≫ (D.complexZ.XIsoOfEq rfl).hom ≫
      cechAugBi D.complexZ ((0 : ℕ) : ℤ)).app W' s')).down = _
  rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  have e := congrArg (fun φ ↦ (φ.app W' ((D.toComplexZ 0 W') (c₀.app W' s'))).down)
    (cechAugBi_cechBiπ (U := U) D.complexZ ((0 : ℕ) : ℤ) (fun _ ↦ α))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e ⊢
  exact e.trans (cechAug_π_app _ _ W' _)

end DegreeZero

/-! ### The decomposition from Čech cocycles -/

section Decomposition

variable {κ : Type u} {U : κ → V.Opens}

omit [Fact p.Prime] [CharP k p] [PerfectField k] [IsProper f] [SmoothOfRelativeDimension n f]
  [Fintype ι] in
/-- The cohomology in degree `m` of `M[-q]` vanishes for `m ≠ q`. -/
theorem isZero_homologyFunctor_singleFunctor_obj (M : V.Modules) {q m : ℤ} (h : q ≠ m) :
    IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
      ((DerivedCategory.singleFunctor V.Modules q).obj M)) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor V.Modules m).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ V.Modules q).app M) ≪≫
    (DerivedCategory.homologyFunctorFactors V.Modules m).app _)
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    (HomologicalComplex.exactAt_single_obj _ q M m (Ne.symm h))

/-- The terms of `F_*K^•`, extended to `ℤ`, vanish outside the degrees `0, …, n`. -/
theorem isZero_complexZ_X {m : ℤ} (hm : ∀ q : Fin (n + 1), ((q : ℕ) : ℤ) ≠ m) :
    IsZero (D.complexZ.X m) := by
  rcases lt_or_ge m 0 with h | h
  · exact D.complex.isZero_extend_X ComplexShape.embeddingUpNat m fun i hi ↦ by
      have : (0 : ℤ) ≤ i := Int.natCast_nonneg i
      change (i : ℤ) = m at hi
      omega
  · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le h
    have hm' : n < m' := by
      by_contra hc
      exact hm ⟨m', by omega⟩ rfl
    refine IsZero.of_iso ?_ (D.complexZXIso m')
    exact (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map_isZero
      (D.isZero_K_of_lt hm')

/-- **The Deligne–Illusie decomposition from Čech cocycles.** Čech cocycles `Ψ q` of total degree
`q` on `K^q`, `q ≤ n`, representing the inverse Cartier map give an isomorphism
`⨁_{q ≤ n} K^q[-q] ≅ F_*K^•` in the derived category. -/
theorem nonempty_iso_of_isCartierCocycle (hU : ⨆ i, U i = ⊤)
    (Ψ : ∀ q : Fin (n + 1), CechCocycleData U D.complexZ (D.K q) ((q : ℕ) : ℤ))
    (hΨ : ∀ q : Fin (n + 1), D.IsCartierCocycle q (Ψ q)) :
    Nonempty ((⨁ fun q : Fin (n + 1) ↦
        (DerivedCategory.singleFunctor V.Modules ((q : ℕ) : ℤ)).obj (D.K q)) ≅
      DerivedCategory.Q.obj D.complexZ) := by
  classical
  set X : Fin (n + 1) → DerivedCategory V.Modules :=
    fun q ↦ (DerivedCategory.singleFunctor V.Modules ((q : ℕ) : ℤ)).obj (D.K q)
  let ψ : (⨁ X) ⟶ DerivedCategory.Q.obj D.complexZ :=
    biproduct.desc fun q ↦ (Ψ q).derivedMap hU 0
  suffices IsIso ψ from ⟨asIso ψ⟩
  rw [DerivedCategory.isIso_iff]
  intro m
  set H := DerivedCategory.homologyFunctor V.Modules m
  have hsum : ∀ q : Fin (n + 1), (∀ q' : Fin (n + 1), q' ≠ q → ((q' : ℕ) : ℤ) ≠ m) →
      H.map (biproduct.π X q ≫ biproduct.ι X q) = 𝟙 _ := by
    intro q hq
    have htot := congrArg H.map (biproduct.total (f := X))
    rw [H.map_id, H.map_sum, Finset.sum_eq_single q] at htot
    · exact htot
    · intro q' _ hq'
      rw [H.map_comp, (isZero_homologyFunctor_singleFunctor_obj (D.K q') (hq q' hq')).eq_of_tgt
        (H.map (biproduct.π X q')) 0, Limits.zero_comp]
    · intro h
      exact absurd (Finset.mem_univ q) h
  by_cases hm : ∃ q : Fin (n + 1), ((q : ℕ) : ℤ) = m
  · obtain ⟨q, rfl⟩ := hm
    have hq : ∀ q' : Fin (n + 1), q' ≠ q → ((q' : ℕ) : ℤ) ≠ ((q : ℕ) : ℤ) := by
      intro q' hq' h
      exact hq' (Fin.ext (by exact_mod_cast h))
    have hι : IsIso (H.map (biproduct.ι X q)) :=
      ⟨H.map (biproduct.π X q), by rw [← H.map_comp, biproduct.ι_π_self, H.map_id],
        by rw [← H.map_comp]; exact hsum q hq⟩
    have hc : IsIso (H.map (biproduct.ι X q) ≫ H.map ψ) := by
      rw [← H.map_comp, biproduct.ι_desc, CechCocycleData.homologyFunctor_map_derivedMap]
      have h := D.isIso_homologyMap_of_isCartierCocycle hU (Ψ q) (hΨ q)
      exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' h (Iso.isIso_inv _))
    exact IsIso.of_isIso_comp_left (H.map (biproduct.ι X q)) (H.map ψ)
  · push Not at hm
    have h1 : IsZero (H.obj (⨁ X)) := by
      rw [IsZero.iff_id_eq_zero, ← H.map_id, ← biproduct.total, H.map_sum]
      refine Finset.sum_eq_zero fun q _ ↦ ?_
      rw [H.map_comp, (isZero_homologyFunctor_singleFunctor_obj (D.K q) (hm q)).eq_of_tgt
        (H.map (biproduct.π X q)) 0, Limits.zero_comp]
    have h2 : IsZero (H.obj (DerivedCategory.Q.obj D.complexZ)) :=
      IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ (D.complexZ.sc m)
        (D.isZero_complexZ_X hm)) ((DerivedCategory.homologyFunctorFactors V.Modules m).app _)
    exact isIso_of_source_target_iso_zero _ h1.isoZero h2.isoZero

end Decomposition

end FrobeniusSplittingData

end MMP.DeRham
