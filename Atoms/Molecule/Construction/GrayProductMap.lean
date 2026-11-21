import Atoms.Molecule.Construction.DualMap
import Atoms.Molecule.Construction.GrayProduct

universe u

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

variable {P P' Q Q' R : OGP.{u}}

theorem mem_boundary_Iic_grayProduct (hP : IsRDC P) (hQ : IsRDC Q)
    (a : P) (x : Q) (n : ℕ) (α : Bool) (b : P) (y : Q) :
    ((b, y) : grayProduct P Q) ∈ (grayProduct P Q).boundary (.Iic (a, x)) n α ↔
      ∃ k ≤ n, b ∈ P.boundary (.Iic a) k α ∧
        y ∈ Q.boundary (.Iic x) (n - k) (xor k.bodd α) := by
  rw [LowerSet.Iic_prod]
  exact mem_boundary_prod_of_isGlobular (hP a).isGlobular (hQ x).isGlobular

scoped instance (P Q : OGP.{u}) : TopologicalSpace (P × Q) := (grayProduct P Q).topologicalSpace

scoped instance (P Q : OGP.{u}) : Topology.IsUpperSet (P × Q) := (grayProduct P Q).isUpperSet

scoped instance (P Q : OGP.{u}) : Category (P × Q) := Preorder.smallCategory (grayProduct P Q)

theorem isClosedMap_snd_grayProduct :
    IsClosedMap (fun p : grayProduct P Q => p.2) :=
  IsUpperSet.isClosedMap_iff_fibration.2 fun ⟨a, _⟩ y hy =>
    ⟨(a, y), Prod.mk_le_mk.2 ⟨le_rfl, hy⟩, rfl⟩

theorem monotone_prodMap {f : P → P'} {g : Q → Q'} (hf : Monotone f) (hg : Monotone g) :
    Monotone (α := grayProduct P Q) (β := grayProduct P' Q') fun p => (f p.1, g p.2) :=
  fun _ _ h => Prod.mk_le_mk.2 ⟨hf h.1, hg h.2⟩

theorem isClosedMap_prodMap {f : P → P'} {g : Q → Q'}
    (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (X := grayProduct P Q) (Y := grayProduct P' Q') fun p => (f p.1, g p.2) := by
  refine IsUpperSet.isClosedMap_iff_fibration.2 ?_
  rintro ⟨a, x⟩ ⟨b, w⟩ ⟨hba, hwx⟩
  obtain ⟨c, hca, rfl⟩ := IsUpperSet.isClosedMap_iff_fibration.1 hf hba
  obtain ⟨y, hyx, rfl⟩ := IsUpperSet.isClosedMap_iff_fibration.1 hg hwx
  exact ⟨(c, y), Prod.mk_le_mk.2 ⟨hca, hyx⟩, rfl⟩

theorem functor_isFibered_prodMap {f : P → P'} {g : Q → Q'} (hf : Monotone f) (hg : Monotone g)
    [hf.functor.IsFibered] [hg.functor.IsFibered]
    (hm : Monotone (α := grayProduct P Q) (β := grayProduct P' Q') fun p => (f p.1, g p.2)) :
    hm.functor.IsFibered := by
  refine (Monotone.functor_isFibered_iff _).2 ?_
  rintro ⟨a, x⟩ ⟨b, w⟩ ⟨hba, hwx⟩
  obtain ⟨c, hca, rfl, hcmax⟩ := Monotone.exists_lift hf hba
  obtain ⟨y, hyx, rfl, hymax⟩ := Monotone.exists_lift hg hwx
  exact ⟨(c, y), Prod.mk_le_mk.2 ⟨hca, hyx⟩, rfl, fun ⟨c', z⟩ ⟨hc'a, hzx⟩ ⟨hfc'b, hgzw⟩ =>
    Prod.mk_le_mk.2 ⟨hcmax c' hc'a hfc'b, hymax z hzx hgzw⟩⟩

theorem image_boundary_Iic_prodMap {f : P → P'} {g : Q → Q'}
    (hP : IsRDC P) (hP' : IsRDC P') (hQ : IsRDC Q) (hQ' : IsRDC Q')
    (hbdf : ∀ (a : P) (n : ℕ) (α : Bool),
      f '' P.boundary (.Iic a) n α = P'.boundary (.Iic (f a)) n α)
    (hbdg : ∀ (x : Q) (n : ℕ) (α : Bool),
      g '' Q.boundary (.Iic x) n α = Q'.boundary (.Iic (g x)) n α)
    (a : P) (x : Q) (n : ℕ) (α : Bool) :
    (fun p : grayProduct P Q => ((f p.1, g p.2) : grayProduct P' Q')) ''
        (grayProduct P Q).boundary (.Iic (a, x)) n α =
      (grayProduct P' Q').boundary (.Iic (f a, g x)) n α := by
  ext ⟨b, w⟩
  constructor
  · rintro ⟨⟨c, y⟩, hy, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨k, hk, hck, hyk⟩ := (mem_boundary_Iic_grayProduct hP hQ a x n α c y).1 hy
    exact (mem_boundary_Iic_grayProduct hP' hQ' (f a) (g x) n α (f c) (g y)).2 ⟨k, hk,
      (hbdf a k α).subset (mem_image_of_mem f hck), (hbdg x _ _).subset (mem_image_of_mem g hyk)⟩
  · intro h
    obtain ⟨k, hk, hbk, hwk⟩ := (mem_boundary_Iic_grayProduct hP' hQ' (f a) (g x) n α b w).1 h
    obtain ⟨c, hc, rfl⟩ := (hbdf a k α).symm.subset hbk
    obtain ⟨y, hy, rfl⟩ := (hbdg x _ _).symm.subset hwk
    exact ⟨(c, y), (mem_boundary_Iic_grayProduct hP hQ a x n α c y).2 ⟨k, hk, hc, hy⟩, rfl⟩

theorem finalOn_of_fibration {f : P → Q} (hf : IsClosedMap f) {S : LowerSet P} {T : Set Q}
    (hST : f '' (S : Set P) = T)
    (hzz : ∀ y ∈ S, ∀ z ∈ S, f y = f z →
      Relation.ReflTransGen (fun a b => a ∈ (S : Set P) ∩ f ⁻¹' Ici (f y) ∧
        b ∈ (S : Set P) ∩ f ⁻¹' Ici (f y) ∧ (a ≤ b ∨ b ≤ a)) y z) :
    FinalOn f S T := by
  have hfib := IsUpperSet.isClosedMap_iff_fibration.1 hf
  refine ⟨hST ▸ mapsTo_image f S, fun w hw => ?_⟩
  obtain ⟨y₀, hy₀, rfl⟩ := hST ▸ hw
  refine ⟨⟨y₀, hy₀, le_rfl⟩,
    IsUpperSet.isPreconnected_iff_reflTransGen.2 fun a ha b hb => ?_⟩
  obtain ⟨a', ha'a, ha'eq⟩ := hfib ha.2
  obtain ⟨b', hb'b, hb'eq⟩ := hfib hb.2
  have ha'S : a' ∈ S := S.lower ha'a ha.1
  have hb'S : b' ∈ S := S.lower hb'b hb.1
  have ha' : a' ∈ (S : Set P) ∩ f ⁻¹' Ici (f y₀) := ⟨ha'S, ha'eq.symm.le⟩
  have hb' : b' ∈ (S : Set P) ∩ f ⁻¹' Ici (f y₀) := ⟨hb'S, hb'eq.symm.le⟩
  have hmid := hzz a' ha'S b' hb'S (ha'eq.trans hb'eq.symm)
  rw [ha'eq] at hmid
  exact (Relation.ReflTransGen.single ⟨ha, ha', Or.inr ha'a⟩).trans
    (hmid.tail ⟨hb', hb, Or.inl hb'b⟩)

theorem isMap_prod_right_of_isMap (hP : IsRDC P) (hQ : IsRDC Q) (hR : IsRDC R)
    {f : Q → R} (hf : IsMap f) :
    IsMap (P := grayProduct P Q) (Q := grayProduct P R) fun p => (p.1, f p.2) := by
  have hcl : IsClosedMap (X := grayProduct P Q) (Y := grayProduct P R) fun p => (p.1, f p.2) :=
    isClosedMap_prodMap IsClosedMap.id hf.isClosedMap
  refine ⟨hcl, fun ⟨a, x⟩ n α => finalOn_of_fibration hcl
    (image_boundary_Iic_prodMap hP hP hQ hR (IsMap.id P).image_boundary hf.image_boundary a x n α)
    ?_⟩
  rintro ⟨b, y⟩ hy ⟨b', z⟩ hz h
  obtain ⟨rfl, hfyz⟩ := Prod.mk.inj h
  have hmem := mem_boundary_Iic_grayProduct hP hQ a x n α
  have hgx := (hQ x).isGlobular
  obtain ⟨k, hkn, hbk, hyk⟩ := (hmem b y).1 hy
  obtain ⟨j, hjn, hbj, hzj⟩ := (hmem b z).1 hz
  have key : ∀ {k j : ℕ}, k ≤ j → j ≤ n → ∀ {v : Q},
      v ∈ Q.boundary (.Iic x) (n - j) (xor j.bodd α) →
      v ∈ Q.boundary (.Iic x) (n - k) (xor k.bodd α) := fun hkj hjn _ hv =>
    (eq_or_lt_of_le hkj).elim (fun h => h ▸ hv) fun _ =>
      hgx.boundary_le_boundary (by omega) _ _ hv
  have hzz : ∀ {m : ℕ}, m ≤ n → b ∈ P.boundary (.Iic a) m α →
      y ∈ Q.boundary (.Iic x) (n - m) (xor m.bodd α) →
      z ∈ Q.boundary (.Iic x) (n - m) (xor m.bodd α) →
      Relation.ReflTransGen (fun p q : grayProduct P Q =>
        p ∈ ((grayProduct P Q).boundary (.Iic (a, x)) n α : Set (grayProduct P Q)) ∩
          (fun p : grayProduct P Q => ((p.1, f p.2) : grayProduct P R)) ⁻¹' Ici (b, f y) ∧
        q ∈ ((grayProduct P Q).boundary (.Iic (a, x)) n α : Set (grayProduct P Q)) ∩
          (fun p : grayProduct P Q => ((p.1, f p.2) : grayProduct P R)) ⁻¹' Ici (b, f y) ∧
        (p ≤ q ∨ q ≤ p)) (b, y) (b, z) := by
    intro m hm hbm hym hzm
    have hfin := hf.finalOn x (n - m) (xor m.bodd α)
    have hconn := IsUpperSet.isPreconnected_iff_reflTransGen.1 (hfin.2 (f y) (hfin.1 hym)).2
      y ⟨hym, le_rfl⟩ z ⟨hzm, hfyz.le⟩
    exact Relation.ReflTransGen.lift (fun u => ((b, u) : grayProduct P Q))
      (fun u v huv => ⟨⟨(hmem b u).2 ⟨m, hm, hbm, huv.1.1⟩, le_rfl, huv.1.2⟩,
        ⟨(hmem b v).2 ⟨m, hm, hbm, huv.2.1.1⟩, le_rfl, huv.2.1.2⟩,
        huv.2.2.imp (fun h => ⟨le_rfl, h⟩) (fun h => ⟨le_rfl, h⟩)⟩) y z hconn
  rcases le_total k j with hkj | hjk
  · exact hzz hkn hbk hyk (key hkj hjn hzj)
  · exact hzz hjn hbj (key hjk hkn hyk) hzj

theorem isMap_prod_left_of_isMap (hP : IsRDC P) (hQ : IsRDC Q) (hR : IsRDC R)
    {f : P → Q} (hf : IsMap f) :
    IsMap (P := grayProduct P R) (Q := grayProduct Q R) fun p => (f p.1, p.2) :=
  (isMap_dual_iff Nat.bodd).1 (((isMap_of_isInclusion (grayProductSwap P R).hom).comp
    (isMap_prod_right_of_isMap (hR.dual Nat.bodd) (hP.dual Nat.bodd) (hQ.dual Nat.bodd)
      (hf.dual Nat.bodd))).comp (isMap_of_isInclusion (grayProductSwap Q R).inv))

theorem isMap_prodMap (hP : IsRDC P) (hP' : IsRDC P') (hQ : IsRDC Q) (hQ' : IsRDC Q')
    {f : P → P'} {g : Q → Q'} (hf : IsMap f) (hg : IsMap g) :
    IsMap (P := grayProduct P Q) (Q := grayProduct P' Q') fun p => (f p.1, g p.2) :=
  (isMap_prod_left_of_isMap hP hP' hQ hf).comp (isMap_prod_right_of_isMap hP' hQ hQ' hg)

theorem isMorphism_prodMap {f : P → P'} {g : Q → Q'} (hf : IsMorphism f) (hg : IsMorphism g) :
    IsMorphism (P := grayProduct P Q) (Q := grayProduct P' Q') fun p => (f p.1, g p.2) := by
  refine ⟨fun ⟨x, y⟩ α => ⟨fun ⟨a, b⟩ h => ?_, fun ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ he => ?_,
    fun ⟨a', b'⟩ h => ?_⟩⟩
  · rw [mem_faces_grayProduct, hf.grade_eq]
    rcases mem_faces_grayProduct.1 h with ⟨ha, rfl⟩ | ⟨rfl, hb⟩
    · exact .inl ⟨(hf.bijOn_faces x α).mapsTo ha, rfl⟩
    · exact .inr ⟨rfl, (hg.bijOn_faces y _).mapsTo hb⟩
  · obtain ⟨hfa, hgb⟩ := Prod.mk.inj he
    rcases mem_faces_grayProduct.1 h₁ with ⟨ha₁, hb₁⟩ | ⟨ha₁, hb₁⟩ <;>
      rcases mem_faces_grayProduct.1 h₂ with ⟨ha₂, hb₂⟩ | ⟨ha₂, hb₂⟩
    · exact Prod.ext ((hf.bijOn_faces x α).injOn ha₁ ha₂ hfa) (hb₁.trans hb₂.symm)
    · exact absurd (hfa.trans (congrArg f ha₂)) ((hf.bijOn_faces x α).mapsTo ha₁).1.ne
    · exact absurd ((congrArg f ha₁).symm.trans hfa) ((hf.bijOn_faces x α).mapsTo ha₂).1.ne'
    · exact Prod.ext (ha₁.trans ha₂.symm) ((hg.bijOn_faces y _).injOn hb₁ hb₂ hgb)
  · rw [mem_faces_grayProduct, hf.grade_eq] at h
    rcases h with ⟨ha', rfl⟩ | ⟨rfl, hb'⟩
    · obtain ⟨a, ha, rfl⟩ := (hf.bijOn_faces x α).surjOn ha'
      exact ⟨(a, y), mem_faces_grayProduct.2 (.inl ⟨ha, rfl⟩), rfl⟩
    · obtain ⟨b, hb, rfl⟩ := (hg.bijOn_faces y _).surjOn hb'
      exact ⟨(x, b), mem_faces_grayProduct.2 (.inr ⟨rfl, hb⟩), rfl⟩

theorem IsLocalEmbedding.prodMap {P P' Q Q' : OGP.{u}} {f : P → P'} {g : Q → Q'}
    (hf : IsLocalEmbedding f) (hg : IsLocalEmbedding g) :
    IsLocalEmbedding (P := grayProduct P Q) (Q := grayProduct P' Q')
      fun p => (f p.1, g p.2) := by
  intro p
  have hm := monotone_prodMap hf.monotone hg.monotone
  refine .of_continuous_injective_isClosedMap
    ((IsUpperSet.monotone_iff_continuous.1 hm).comp continuous_subtype_val) ?_
    ((isClosedMap_prodMap hf.isClosedMap hg.isClosedMap).comp
      isClosed_closure.isClosedMap_subtype_val)
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
  have hab₀ := hab
  have hab₀' := hab'
  rw [IsUpperSet.closure_singleton] at hab₀ hab₀'
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  have ha := (hf p.1).injective (a₁ := ⟨a, by rw [IsUpperSet.closure_singleton]; exact hab₀.1⟩)
    (a₂ := ⟨a', by rw [IsUpperSet.closure_singleton]; exact hab₀'.1⟩) h₁
  have hb := (hg p.2).injective (a₁ := ⟨b, by rw [IsUpperSet.closure_singleton]; exact hab₀.2⟩)
    (a₂ := ⟨b', by rw [IsUpperSet.closure_singleton]; exact hab₀'.2⟩) h₂
  exact Subtype.ext (Prod.ext (congrArg Subtype.val ha) (congrArg Subtype.val hb))

end Atoms.Molecule.OGP
