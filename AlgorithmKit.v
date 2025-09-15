From Stdlib Require Import List.
Import ListNotations.

Module Type SymmetricCipher.
  Parameter Plaintext  : Type.
  Parameter Ciphertext : Type.
  Parameter Key        : Type.

  Parameter keygen  : Key.
  Parameter encrypt : Key -> Plaintext -> Ciphertext.
  Parameter decrypt : Key -> Ciphertext -> Plaintext.

  Axiom decrypt_encrypt_inverse :
    forall k p, decrypt k (encrypt k p) = p.
End SymmetricCipher.

Module Type AsymmetricCipher.
  Parameter Plaintext  : Type.
  Parameter Ciphertext : Type.
  Parameter PublicKey  : Type.
  Parameter PrivateKey : Type.

  Parameter keypair  : PublicKey * PrivateKey.
  Parameter encrypt  : PublicKey -> Plaintext -> Ciphertext.
  Parameter decrypt  : PrivateKey -> Ciphertext -> Plaintext.

  Definition pubkey  := fst keypair.
  Definition privkey := snd keypair.

End AsymmetricCipher.

Module Type HashFunction.
  Parameter Input  : Type.
  Parameter Digest : Type.
  Parameter hash   : Input -> Digest.  (* 这里的 hash 是本模块内“固定”的具体哈希函数 *)

  Parameter SolveHashPreimage : Type.

  (* 对目标输入 x，生成有限候选 preimage 集合 *)
  Parameter produce_preimage :
    SolveHashPreimage -> (Input -> Digest) -> Input -> list Input.

  (* 验证给定目标 x 上该思路是否成功（布尔） *)
  Parameter crack_preimage  :
    SolveHashPreimage -> (Input -> Digest) -> Input -> bool.

  (** 规范：对“本模块固定的 hash”，verify=true 当且仅当候选集中有匹配项。 *)
  Axiom crack_preimage_iff :
    forall (s : SolveHashPreimage) (x : Input),
      crack_preimage s hash x = true <->
      exists y, In y (produce_preimage s hash x) /\ hash x = hash y.

  (** =============== 点态（per‑input）定义 =============== *)
  Definition ReverseAt (x : Input) : Prop :=
    exists s, crack_preimage s hash x = true.

  Definition ReverseFreeAt (x : Input) : Prop :=
    forall s, crack_preimage s hash x = false.

  (** 可选：整体安全性（对所有输入都不可逆） *)
  Definition Secure : Prop := forall x, ReverseFreeAt x.

  (** 关键引理：在固定的 hash 下，
      “无候选” ⇔ “对所有 s 验证都为 false”。 *)
  Lemma no_candidate_iff_all_crack_false_at :
    forall (x : Input),
      (~ exists s y, In y (produce_preimage s hash x) /\ hash y = hash x)
      <->
      (forall s, crack_preimage s hash x = false).
  Proof.
    intro x; split.
    - (* 无候选 -> 每个 s 都 verify=false *)
      intros Hnone s.
      destruct (crack_preimage s hash x) eqn:Hv.
      + (* 这里 verify = true，目标是证明 true = false，
           我们先由 Hv 和 iff 得到存在性，然后用 Hnone 得到 False，再用 exfalso 结束。 *)
        apply (proj1 (crack_preimage_iff s x)) in Hv.
        destruct Hv as [y [Hin Heq]].
        exfalso.
        apply Hnone.
        exists s, y; split; auto.
      + (* verify = false 分支直接完成 *)
        reflexivity.
    - (* forall s, verify=false -> 无候选 *)
      intros Hforall [s [y [Hin Heq]]].
      specialize (Hforall s).
      (* 由存在候选，用 iff 的另一方向推出 verify=true，与 Hforall 矛盾 *)
      assert (Hv : crack_preimage s hash x = true).
      { apply (proj2 (crack_preimage_iff s x)). exists y; split; [assumption | symmetry; assumption]. }
      rewrite Hv in Hforall. discriminate.
  Qed.

  (** 若对 data 点态安全（所有 s 验证为 false），则候选集中不可能出现匹配项。 *)
  Lemma goal_formulation_for_fixed_data :
    forall (data : Input),
      (forall s, crack_preimage s hash data = false) ->
      ~(exists s d, In d (produce_preimage s hash data) /\ hash d = hash data).
  Proof.
    intros data H.
    apply (proj2 (no_candidate_iff_all_crack_false_at data)).
    exact H.
  Qed.

  (** 衍生：若整体安全（Secure），则对任意 data 都满足上面的否定式目标。 *)
  Lemma secure_implies_goal_for_all_data :
    Secure -> forall data,
      ~(exists s d, In d (produce_preimage s hash data) /\ hash d = hash data).
  Proof.
    intros Hsec data.
    apply (goal_formulation_for_fixed_data data).
    unfold Secure, ReverseFreeAt in Hsec.
    apply Hsec.
  Qed.

End HashFunction.

Module Type DigitalSignature.
  Parameter Message    : Type.
  Parameter Signature  : Type.
  Parameter PublicKey  : Type.
  Parameter PrivateKey : Type.

  Parameter keypair : PublicKey * PrivateKey.
  Definition pubkey  := fst keypair.
  Definition privkey := snd keypair.

  Parameter sign   : PrivateKey -> Message -> Signature.
  Parameter verify : PublicKey  -> Message -> Signature -> bool.

  Axiom verify_sign_correct :
    forall m, verify pubkey m (sign privkey m) = true.

  (* 攻击思路类型：攻击者想要针对给定消息 m 伪造签名 *)
  Parameter SolveSig : Type.

  (* 给定攻击思路 s、验证函数 verify（含公钥）、消息 m，产生签名候选集 *)
  Parameter produce_signature :
    SolveSig -> (PublicKey -> Message -> Signature -> bool) -> Message -> list Signature.

  (* 验证：verify pub m sig 是否为 true *)
  Parameter crack_signature :
    SolveSig -> (PublicKey -> Message -> Signature -> bool) -> Message -> bool.

  Axiom crack_signature_iff :
    forall (s : SolveSig) (m : Message),
      crack_signature s verify m = true <->
        exists sigma, In sigma (produce_signature s verify m) /\ verify pubkey m sigma = true.

  (** 点态定义：在没有私钥的情况下，能否伪造 m 的有效签名 *)
  Definition ForgeAt (m : Message) : Prop := exists s, crack_signature s verify m = true.
  Definition ForgeFreeAt (m : Message) : Prop := forall s, crack_signature s verify m = false.

  Definition Secure : Prop := forall m, ForgeFreeAt m.

  Lemma no_candidate_iff_all_crack_false_at :
    forall (m : Message),
      (~ exists s sigma, In sigma (produce_signature s verify m) /\ verify pubkey m sigma = true)
      <-> (forall s, crack_signature s verify m = false).
  Proof.
    intro m; split.
    - intros Hnone s.
      destruct (crack_signature s verify m) eqn:Hv.
      + apply (proj1 (crack_signature_iff s m)) in Hv.
        destruct Hv as [sig [Hin Heq]].
        exfalso; apply Hnone; exists s, sig; split; auto.
      + reflexivity.
    - intros Hforall [s [sig [Hin Heq]]].
      specialize (Hforall s).
      assert (Hv : crack_signature s verify m = true).
      { apply (proj2 (crack_signature_iff s m)). exists sig; split; [assumption | assumption]. }
      rewrite Hv in Hforall. discriminate.
  Qed.

  Lemma goal_formulation_for_fixed_message :
    forall (m : Message),
      (forall s, crack_signature s verify m = false) ->
      ~(exists s sigma, In sigma (produce_signature s verify m) /\ verify pubkey m sigma = true).
  Proof.
    intros m H.
    apply (proj2 (no_candidate_iff_all_crack_false_at m)).
    exact H.
  Qed.

  Lemma goal_formulation_for_fixed_message_exists_true :
    forall (m : Message),
      (exists s sigma, In sigma (produce_signature s verify m) /\ verify pubkey m sigma = true) ->
      exists s, crack_signature s verify m = true.
  Proof.
    intros m [s [sigma [Hin Hver]]].
    exists s.
    apply (proj2 (crack_signature_iff s m)).
    exists sigma; split; assumption.
  Qed.

  Lemma secure_implies_goal_for_all_messages :
    Secure -> forall m,
      ~(exists s sigma, In sigma (produce_signature s verify m) /\ verify pubkey m sigma = true).
  Proof.
    intros Hsec m.
    apply (goal_formulation_for_fixed_message m).
    unfold Secure, ForgeFreeAt in Hsec.
    apply Hsec.
  Qed.

End DigitalSignature.

Module Type KDFunction.
  Parameter Input  : Type.
  Parameter Output : Type.
  Parameter kdf : Input -> Output.
End KDFunction.
