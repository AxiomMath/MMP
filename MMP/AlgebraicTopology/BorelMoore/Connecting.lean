module

public import MMP.AlgebraicTopology.BorelMoore.LongExactHomotopy
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductNatural
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# The connecting map of the Borel–Moore long exact sequence (Fulton, §19.1)

For a closed subset `X` of a Hausdorff space `Y` with `U = Y - X` and the relative
quasi-isomorphism `C^lf(Y) / C^lf(X) → C^lf(U)` (`borelMooreHomology.IsRelativeQuasiIso`), the
*connecting map* `∂ : H_{k+1} U → H_k X` (`borelMooreHomology.connecting`) is the snake map of
`0 → C^lf X → C^lf Y → C^lf Y / C^lf X → 0` after the inverse of the quasi-isomorphism. It makes
`⋯ → H_{k+1} U → H_k X → H_k Y → H_k U → H_{k-1} X → ⋯` exact, and on chains: for a cycle `w`
of `U` and a chain `b` of `Y` with `b|_U - w` a boundary of `U` and `∂ b = i_* a`,
`∂ [w] = [a]` (`borelMooreHomology.connecting_homologyEquiv_symm_mk`).

## Main definitions

* `MMP.ModuleCatComplex.quasiIsoConnecting`: the connecting map of a monomorphism `f` and a map `g`
  with `f ≫ g = 0` whose induced map on `coker f` is a quasi-isomorphism.
* `MMP.borelMooreHomology.connecting`: `∂ : H_{k+1} U → H_k X`.

## Main results

* `MMP.ModuleCatComplex.quasiIsoConnecting_apply`: `δ [g x₂] = [x₁]` when `f x₁ = d x₂`.
* `MMP.borelMooreHomology.exact_connecting_pushforward`,
  `exact_pushforward_restrict`, `exact_restrict_connecting`: the long exact sequence.
* `MMP.borelMooreHomology.connecting_homologyEquiv_symm_mk`: the chain-level
  description of `∂`.
* `MMP.borelMooreHomology.connecting_homologyEquiv_symm_mk_of_fill`: the same when
  `∂ b` is a cycle `β` of a closed `B ⊆ N - X` only, `N` a neighbourhood deformed into `X` by
  `G`: then `∂ [w] = [G(·, 1)_* β]` if `b|_U - H β - w` is a boundary (`H = deformOp`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, (3).
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace MMP.ModuleCatComplex

open _root_.HomologicalComplex

variable {R : Type u} [CommRing R]
  {A B D : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up ℤ)}
  (f : A ⟶ B) (g : B ⟶ D) [Mono f] (w : f ≫ g = 0)

/-- The short exact sequence `0 → A → B → coker f → 0` of a monomorphism. -/
lemma shortExact_cokernel :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
  { exact := ShortComplex.exact_cokernel f }

/-- The connecting map `H^i D → H^j A` of a monomorphism `f : A ⟶ B` and `g : B ⟶ D` with
`f ≫ g = 0` whose induced map `coker f ⟶ D` is a quasi-isomorphism: the inverse of that
quasi-isomorphism on homology, followed by the connecting map of `0 → A → B → coker f → 0`. -/
def quasiIsoConnecting [QuasiIso (cokernel.desc f g w)] (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) : D.homology i ⟶ A.homology j :=
  inv (homologyMap (cokernel.desc f g w) i) ≫ (shortExact_cokernel f).δ i j hij

/-- **The connecting map on elements**: if `f x₁ = d x₂`, the connecting map sends the class of
the cycle `g x₂` to the class of `x₁`. -/
lemma quasiIsoConnecting_apply [QuasiIso (cokernel.desc f g w)] (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) (x₂ : B.X i) (x₃ : D.X i) (hx₂ : (g.f i).hom x₂ = x₃)
    (hx₃ : (D.d i j).hom x₃ = 0) (x₁ : A.X j) (hx₁ : (f.f j).hom x₁ = (B.d i j).hom x₂)
    (k : ℤ) (hk : (ComplexShape.up ℤ).next j = k) :
    (quasiIsoConnecting f g w i j hij).hom
        ((D.homologyπ i).hom (D.cyclesMk x₃ j ((ComplexShape.up ℤ).next_eq' hij) hx₃)) =
      (A.homologyπ j).hom (A.cyclesMk x₁ k hk
        ((shortExact_cokernel f).d_eq_zero_of_f_eq_d_apply i j x₂ x₁ hx₁ k)) := by
  subst hx₂
  set φ := cokernel.desc f g w
  have hS := shortExact_cokernel f
  have hφ : ∀ y, (φ.f i).hom (((cokernel.π f).f i).hom y) = (g.f i).hom y := fun y ↦ by
    rw [← ModuleCat.comp_apply, ← comp_f, cokernel.π_desc]
  have h3 : ((cokernel f).d i j).hom (((cokernel.π f).f i).hom x₂) = 0 := by
    rw [← ModuleCat.comp_apply, Hom.comm, ModuleCat.comp_apply, ← hx₁, ← ModuleCat.comp_apply,
      ← comp_f, cokernel.condition, zero_f]
    rfl
  have key := hS.δ_apply i j hij (((cokernel.π f).f i).hom x₂) h3 x₂ rfl x₁ hx₁ k hk
  have hcyc : (cyclesMap φ i).hom ((cokernel f).cyclesMk (((cokernel.π f).f i).hom x₂) j
      ((ComplexShape.up ℤ).next_eq' hij) h3) =
      D.cyclesMk ((g.f i).hom x₂) j ((ComplexShape.up ℤ).next_eq' hij) hx₃ := by
    apply (ModuleCat.mono_iff_injective (D.iCycles i)).1 inferInstance
    rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply]
    have h1 := (cokernel f).i_cyclesMk (((cokernel.π f).f i).hom x₂) j
      ((ComplexShape.up ℤ).next_eq' hij) h3
    have h2 := D.i_cyclesMk ((g.f i).hom x₂) j ((ComplexShape.up ℤ).next_eq' hij) hx₃
    exact ((congrArg (φ.f i).hom h1).trans (hφ x₂)).trans h2.symm
  have hπ : (D.homologyπ i).hom
      (D.cyclesMk ((g.f i).hom x₂) j ((ComplexShape.up ℤ).next_eq' hij) hx₃) =
      (homologyMap φ i).hom (((cokernel f).homologyπ i).hom ((cokernel f).cyclesMk
        (((cokernel.π f).f i).hom x₂) j ((ComplexShape.up ℤ).next_eq' hij) h3)) := by
    rw [← hcyc]
    exact (ConcreteCategory.congr_hom (homologyπ_naturality φ i) _).symm
  rw [hπ, quasiIsoConnecting, ModuleCat.comp_apply, ← ModuleCat.comp_apply (homologyMap φ i),
    IsIso.hom_inv_id, ModuleCat.id_apply]
  exact key

section exact

variable [QuasiIso (cokernel.desc f g w)]

private lemma function_exact {S' : ShortComplex (ModuleCat.{u} R)} (h : S'.Exact) :
    Function.Exact S'.f.hom S'.g.hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h

private lemma inv_hom_apply (i : ℤ) (x : (cokernel f).homology i) :
    (inv (homologyMap (cokernel.desc f g w) i)).hom
      ((homologyMap (cokernel.desc f g w) i).hom x) = x := by
  rw [← ModuleCat.comp_apply, IsIso.hom_inv_id, ModuleCat.id_apply]

private lemma hom_inv_apply (i : ℤ) (x : D.homology i) :
    (homologyMap (cokernel.desc f g w) i).hom
      ((inv (homologyMap (cokernel.desc f g w) i)).hom x) = x := by
  rw [← ModuleCat.comp_apply, IsIso.inv_hom_id, ModuleCat.id_apply]

private lemma homologyMap_g (i : ℤ) :
    homologyMap g i = homologyMap (cokernel.π f) i ≫ homologyMap (cokernel.desc f g w) i := by
  rw [← homologyMap_comp, cokernel.π_desc]

/-- Exactness of `H^i D → H^j A → H^j B`. -/
lemma exact_quasiIsoConnecting_homologyMap (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    Function.Exact (quasiIsoConnecting f g w i j hij).hom (homologyMap f j).hom := by
  intro y
  refine (function_exact ((shortExact_cokernel f).homology_exact₁ i j hij) y).trans ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(homologyMap (cokernel.desc f g w) i).hom x, by
      rw [quasiIsoConnecting, ModuleCat.comp_apply, inv_hom_apply]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩

include w in
/-- Exactness of `H^i A → H^i B → H^i D`. -/
lemma exact_homologyMap_homologyMap (i : ℤ) :
    Function.Exact (homologyMap f i).hom (homologyMap g i).hom := by
  rw [homologyMap_g f g w i, ModuleCat.hom_comp, LinearMap.coe_comp]
  refine (function_exact ((shortExact_cokernel f).homology_exact₂ i)).comp_injective _ ?_
    (map_zero _)
  intro x x' hx
  have := congrArg (inv (homologyMap (cokernel.desc f g w) i)).hom hx
  rwa [inv_hom_apply, inv_hom_apply] at this

/-- Exactness of `H^i B → H^i D → H^j A`. -/
lemma exact_homologyMap_quasiIsoConnecting (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    Function.Exact (homologyMap g i).hom (quasiIsoConnecting f g w i j hij).hom := by
  intro y
  refine (function_exact ((shortExact_cokernel f).homology_exact₃ i j hij)
    ((inv (homologyMap (cokernel.desc f g w) i)).hom y)).trans ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [homologyMap_g f g w i, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    change (homologyMap (cokernel.π f) i).hom x = _ at hx
    rw [hx, hom_inv_apply]
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    rw [homologyMap_g f g w i, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    exact (inv_hom_apply f g w i _).symm

end exact

end MMP.ModuleCatComplex

namespace MMP

namespace borelMooreHomology

open LocallyFiniteChain BorelMooreCross

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y]
  {X : Set Y} (hX : IsClosed X)

/-- In the cohomological complex shape on `ℤ`, the degree `-(k + 1)` is related to `-k`. -/
lemma rel_neg_succ_neg (k : ℤ) : (ComplexShape.up ℤ).Rel (-(k + 1)) (-k) := by
  simp only [ComplexShape.up_Rel]
  ring

/-- The *connecting map* `∂ : H_{k+1} U → H_k X` of the Borel–Moore long exact sequence of a
closed subset `X` of `Y` with `U = Y - X`, given the relative quasi-isomorphism
`C^lf(Y) / C^lf(X) → C^lf(U)`: the snake map of `0 → C^lf X → C^lf Y → C^lf Y / C^lf X → 0`
after the inverse of that quasi-isomorphism. -/
def connecting (h : IsRelativeQuasiIso R M hX) (k : ℤ) :
    borelMooreHomology R M (TopCat.of (complOpens hX)) (k + 1) ⟶
      borelMooreHomology R M (TopCat.of X) k :=
  haveI : QuasiIso _ := h
  MMP.ModuleCatComplex.quasiIsoConnecting (extIncl R M hX) (extRestrict R M hX)
    (extIncl_comp_extRestrict R M hX) (-(k + 1)) (-k) (rel_neg_succ_neg k)

variable {R M hX} (h : IsRelativeQuasiIso R M hX)

/-- Exactness of `H_{k+1} U → H_k X → H_k Y`. -/
theorem exact_connecting_pushforward (k : ℤ) :
    Function.Exact (connecting R M hX h k).hom
      (pushforward R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX) k).hom :=
  haveI : QuasiIso _ := h
  MMP.ModuleCatComplex.exact_quasiIsoConnecting_homologyMap _ _ _ _ _ _

include h in
/-- Exactness of `H_k X → H_k Y → H_k U`. -/
theorem exact_pushforward_restrict (k : ℤ) :
    Function.Exact
      (pushforward R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX) k).hom
      (restrict R M (complOpens hX) k).hom :=
  haveI : QuasiIso _ := h
  MMP.ModuleCatComplex.exact_homologyMap_homologyMap _ _ (extIncl_comp_extRestrict R M hX) _

/-- Exactness of `H_{k+1} Y → H_{k+1} U → H_k X`. -/
theorem exact_restrict_connecting (k : ℤ) :
    Function.Exact (restrict R M (complOpens hX) (k + 1)).hom (connecting R M hX h k).hom :=
  haveI : QuasiIso _ := h
  MMP.ModuleCatComplex.exact_homologyMap_quasiIsoConnecting _ _ _ _ _ _

section chains

/-- The class of a locally finite `n`-cycle `z`, read in the `ℤ`-graded complex: the homology
class of the cycle `z` in degree `-n` of the extended complex. -/
lemma homologyEquiv_symm_mk_eq_homologyπ_extend {Z : TopCat.{u}} {n : ℕ}
    (z : Cyc (R := R) Z n) (hn : ComplexShape.embeddingDownNat.f n = -(n : ℤ)) (j : ℤ)
    (hj : (ComplexShape.up ℤ).next (-(n : ℤ)) = j)
    (hz : (((BM R Z).extend ComplexShape.embeddingDownNat).d (-(n : ℤ)) j).hom
      (((BM R Z).extendXIso ComplexShape.embeddingDownNat hn).inv.hom z.1) = 0) :
    (homologyEquiv R Z n).symm (Submodule.Quotient.mk z) =
      (((BM R Z).extend ComplexShape.embeddingDownNat).homologyπ (-(n : ℤ))).hom
        (((BM R Z).extend ComplexShape.embeddingDownNat).cyclesMk
          (((BM R Z).extendXIso ComplexShape.embeddingDownNat hn).inv.hom z.1) j hj hz) := by
  set K := BM R Z
  set e := ComplexShape.embeddingDownNat
  set c := (K.sc n).moduleCatCyclesIso.inv.hom z
  have h1 : (homologyEquiv R Z n).symm (Submodule.Quotient.mk z) =
      (K.extendHomologyIso e hn).inv.hom ((K.homologyπ n).hom c) := by
    have := congrArg (fun m ↦ m.hom z) (K.sc n).moduleCatCyclesIso_inv_π
    exact (congrArg (K.extendHomologyIso e hn).inv.hom this).symm
  have h2 : (K.extendHomologyIso e hn).inv.hom ((K.homologyπ n).hom c) =
      ((K.extend e).homologyπ (-(n : ℤ))).hom ((K.extendCyclesIso e hn).inv.hom c) := by
    have h := K.homologyπ_extendHomologyIso_hom e hn
    have h' : (K.extendCyclesIso e hn).inv ≫ (K.extend e).homologyπ (-(n : ℤ)) =
        K.homologyπ n ≫ (K.extendHomologyIso e hn).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    exact (ConcreteCategory.congr_hom h' c).symm
  have h3 : (K.extendCyclesIso e hn).inv.hom c =
      (K.extend e).cyclesMk ((K.extendXIso e hn).inv.hom z.1) j hj hz := by
    apply (ModuleCat.mono_iff_injective ((K.extend e).iCycles (-(n : ℤ)))).1 inferInstance
    have h4 := ConcreteCategory.congr_hom (K.extendCyclesIso_inv_iCycles e hn) c
    have h5 := (K.extend e).i_cyclesMk ((K.extendXIso e hn).inv.hom z.1) j hj hz
    refine (h4.trans ?_).trans h5.symm
    change (K.extendXIso e hn).inv.hom ((K.iCycles n).hom c) = _
    congr 1
    exact ShortComplex.moduleCatCyclesIso_inv_iCycles_apply (K.sc n) z
  rw [h1, h2, h3]

/-- **The connecting map on chains.** Let `w` be a locally finite `(k + 1)`-cycle of
`U = Y - X`, and `b` a locally finite chain of `Y` with `b|_U - w = ∂ e` a boundary of `U` and
`∂ b = i_* a` for a chain `a` of `X`. Then `∂ [w] = [a]`. -/
theorem connecting_homologyEquiv_symm_mk (h : IsRelativeQuasiIso R (ModuleCat.of R R) hX)
    (k : ℕ) (w : Cyc (R := R) (TopCat.of (complOpens hX)) (k + 1)) (b : (BM R Y).X (k + 1))
    (a : Cyc (R := R) (TopCat.of X) k)
    (hab : ((chainMap R (ModuleCat.of R R) (subspaceInclusion Y X)
      (isProperMap_subspaceInclusion hX)).f k).hom a.1 = ((BM R Y).d (k + 1) k).hom b)
    (e : (BM R (TopCat.of (complOpens hX))).X (k + 2))
    (hbw : ((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (k + 1)).hom b - w.1 =
      ((BM R (TopCat.of (complOpens hX))).d (k + 2) (k + 1)).hom e) :
    (connecting R (ModuleCat.of R R) hX h k).hom
        ((homologyEquiv R (TopCat.of (complOpens hX)) (k + 1)).symm (Submodule.Quotient.mk w)) =
      (homologyEquiv R (TopCat.of X) k).symm (Submodule.Quotient.mk a) := by
  -- replace `w` by the cycle `b|_U`
  have hw' : ((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (k + 1)).hom b ∈
      Cyc (R := R) (TopCat.of (complOpens hX)) (k + 1) := by
    rw [mem_cyc_iff]
    change ((BM R (TopCat.of (complOpens hX))).d (k + 1) k).hom _ = 0
    have := ConcreteCategory.congr_hom
      ((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).comm (k + 1) k) b
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    refine this.trans ?_
    rw [← hab]
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (chainMap_subspaceInclusion_comp_restrictChainMap R
        (ModuleCat.of R R) hX) k) a.1
  have hmk : (Submodule.Quotient.mk w : HomQ (R := R) (TopCat.of (complOpens hX)) (k + 1)) =
      Submodule.Quotient.mk ⟨_, hw'⟩ := by
    refine ((Submodule.Quotient.eq _).2 ?_).symm
    exact mem_bdry_of (⟨_, hw'⟩ - w) e hbw.symm
  rw [hmk]
  have hU : ComplexShape.embeddingDownNat.f (k + 1) = -((k + 1 : ℕ) : ℤ) := by simp
  have hXk : ComplexShape.embeddingDownNat.f k = -(k : ℤ) := by simp
  have hnext : (ComplexShape.up ℤ).next (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) := by simp
  have hnext' : (ComplexShape.up ℤ).next (-(k : ℤ)) = -(k : ℤ) + 1 := by simp
  set x₂ := ((BM R Y).extendXIso ComplexShape.embeddingDownNat hU).inv.hom b with hx₂def
  set x₁ := ((BM R (TopCat.of X)).extendXIso ComplexShape.embeddingDownNat hXk).inv.hom a.1
    with hx₁def
  have hx₂ : ((extRestrict R (ModuleCat.of R R) hX).f (-((k + 1 : ℕ) : ℤ))).hom x₂ =
      ((BM R (TopCat.of (complOpens hX))).extendXIso ComplexShape.embeddingDownNat hU).inv.hom
        (((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (k + 1)).hom b) := by
    rw [HomologicalComplex.extendMap_f _ _ hU]
    simp [x₂]
  have hx₁ : ((extIncl R (ModuleCat.of R R) hX).f (-(k : ℤ))).hom x₁ =
      (((BM R Y).extend ComplexShape.embeddingDownNat).d (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ))).hom
        x₂ := by
    rw [HomologicalComplex.extendMap_f _ _ hXk, HomologicalComplex.extend_d_eq _ _ hU hXk]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, x₁, x₂]
    have c : ∀ {P Q : ModuleCat.{u} R} (i : P ≅ Q) (x : Q), i.hom.hom (i.inv.hom x) = x :=
      fun i x ↦ by rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
    rw [c, c]
    exact congrArg _ hab
  have hz₃ : (((BM R (TopCat.of (complOpens hX))).extend ComplexShape.embeddingDownNat).d
      (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ))).hom
      (((BM R (TopCat.of (complOpens hX))).extendXIso ComplexShape.embeddingDownNat hU).inv.hom
        (((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (k + 1)).hom b)) = 0 := by
    rw [← hx₂]
    refine (ConcreteCategory.congr_hom
      ((extRestrict R (ModuleCat.of R R) hX).comm (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ))) x₂).trans ?_
    change ((extRestrict R (ModuleCat.of R R) hX).f (-(k : ℤ))).hom
      ((((BM R Y).extend ComplexShape.embeddingDownNat).d (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ))).hom
        x₂) = 0
    rw [← hx₁]
    have := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
      (extIncl_comp_extRestrict R (ModuleCat.of R R) hX) (-(k : ℤ))) x₁
    simpa using this
  haveI : QuasiIso _ := h
  have key := MMP.ModuleCatComplex.quasiIsoConnecting_apply (extIncl R (ModuleCat.of R R) hX)
    (extRestrict R (ModuleCat.of R R) hX) (extIncl_comp_extRestrict R (ModuleCat.of R R) hX)
    (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ)) (rel_neg_succ_neg (k : ℤ)) x₂ _ hx₂ hz₃ x₁ hx₁
    (-(k : ℤ) + 1) hnext'
  refine (congrArg (connecting R (ModuleCat.of R R) hX h k).hom
    (homologyEquiv_symm_mk_eq_homologyπ_extend ⟨_, hw'⟩ hU (-(k : ℤ)) hnext hz₃)).trans ?_
  refine key.trans ?_
  exact (homologyEquiv_symm_mk_eq_homologyπ_extend a hXk _ hnext' _).symm

section fill

variable {N : Set Y} {G : C(N × unitInterval, Y)} (hG : IsProperMap G)
  (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) (hG0 : ∀ y, G (y, 0) = y)
  (hG1 : ∀ y, G (y, 1) ∈ X) {B : Set Y} (hB : IsClosed B) (hBN : B ⊆ N) (hBX : B ⊆ Xᶜ)

/-- **The connecting map on chains, through a deformation.** Let `G : N × I → Y` deform a
neighbourhood `N` of `X` into `X` (fixing `X`), `B ⊆ N - X` closed, `β` a `k`-cycle of `B`, and
`b` a `(k + 1)`-chain of `Y` with `∂ b = β`. If `w` is a `(k + 1)`-cycle of `U = Y - X` with
`b|_U - H β - w` a boundary of `U`, `H` the deformation operator (`deformOp`), then
`∂ [w] = [G(·, 1)_* β]`. -/
theorem connecting_homologyEquiv_symm_mk_of_fill (h : IsRelativeQuasiIso R (ModuleCat.of R R) hX)
    (k : ℕ) (w : Cyc (R := R) (TopCat.of (complOpens hX)) (k + 1)) (b : (BM R Y).X (k + 1))
    (β : Cyc (R := R) (TopCat.of B) k)
    (hb : ((chainMap R (ModuleCat.of R R) (subsetInclusion B) (isProperMap_subsetInclusion hB)).f
      k).hom β.1 = ((BM R Y).d (k + 1) k).hom b)
    (e : (BM R (TopCat.of (complOpens hX))).X (k + 2))
    (hbw : ((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (k + 1)).hom b -
      (deformOp R (ModuleCat.of R R) hX hG hGX k).hom
        (((chainMap R (ModuleCat.of R R) (fillIncl hX hBN hBX)
          (isProperMap_fillIncl hX hB hBN hBX)).f k).hom β.1) - w.1 =
      ((BM R (TopCat.of (complOpens hX))).d (k + 2) (k + 1)).hom e) :
    (connecting R (ModuleCat.of R R) hX h k).hom
        ((homologyEquiv R (TopCat.of (complOpens hX)) (k + 1)).symm (Submodule.Quotient.mk w)) =
      (homologyEquiv R (TopCat.of X) k).symm (Submodule.Quotient.mk
        ⟨((chainMap R (ModuleCat.of R R) (fillEnd hBN hG1)
          (isProperMap_fillEnd hG hB hBN hG0 hG1)).f k).hom β.1,
          chainMap_mem_cyc R _ β⟩) := by
  set hB' := fillChainHomotopy hG hB hBN R (ModuleCat.of R R) hG0 hG1
  refine connecting_homologyEquiv_symm_mk h k w (b - (hB'.hom k (k + 1)).hom β.1) _ ?_ e ?_
  · -- `∂ (h β) = β - G(·, 1)_* β`, `β` being a cycle
    have hcomp := congrArg (fun φ ↦ (φ.f k).hom β.1)
      (chainMap_comp R (ModuleCat.of R R) (fillEnd hBN hG1) (subspaceInclusion Y X)
        (isProperMap_fillEnd hG hB hBN hG0 hG1) (isProperMap_subspaceInclusion hX))
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
    have hβ := (mem_cyc_iff β.1).1 β.2
    have key : ((chainMap R (ModuleCat.of R R) (subsetInclusion B)
        (isProperMap_subsetInclusion hB)).f k).hom β.1 -
        ((chainMap R (ModuleCat.of R R) (fillEnd hBN hG1 ≫ subspaceInclusion Y X)
          ((isProperMap_subspaceInclusion hX).comp (isProperMap_fillEnd hG hB hBN hG0 hG1))).f k).hom
          β.1 = ((BM R Y).d (k + 1) k).hom ((hB'.hom k (k + 1)).hom β.1) := by
      rcases k with _ | k
      · exact MMP.ChainHomotopyAux.apply_zero hB' β.1
      · rw [MMP.ChainHomotopyAux.apply_succ hB' k β.1]
        change ((hB'.hom k (k + 1)).hom (((BM R (TopCat.of B)).d (k + 1) k).hom β.1)) + _ = _
        rw [show ((BM R (TopCat.of B)).d (k + 1) k).hom β.1 = 0 from hβ, map_zero, zero_add]
    rw [map_sub, ← hb, ← key, ← hcomp]
    abel
  · rw [map_sub, restrictChainMap_fillChainHomotopy hX hG hB hBN hBX R (ModuleCat.of R R) hGX
      hG0 hG1 k β.1]
    exact hbw

end fill

end chains

end borelMooreHomology

end MMP
