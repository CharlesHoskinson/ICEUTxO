# Prior art for the Starstream Paradigm: A comprehensive survey

The core concepts described in the "Starstream Paradigm"—coroutinized UTXOs, coordination scripts, algebraic effects, IVC compression, and parallel execution—have substantial prior art across academic literature and blockchain projects dating from **2017-2025**. The foundational frameworks exist, though their specific integration as described in Starstream represents a novel synthesis.

## Stateful UTXOs emerged through Cardano, Ergo, and Nervos CKB

The concept of extending UTXOs to carry execution state has been formalized by three major research efforts. Cardano's **Extended UTXO (EUTXO) model**, published by Chakravarty et al. at Financial Cryptography 2020, is the seminal formalization. It introduces **datum fields** for arbitrary contract state and **validator predicates** receiving full transaction context, enabling UTXOs to implement general state machines. The key theoretical contribution is **Constraint Emitting Machines (CEMs)**—a form of Mealy machine with proven weak bisimulation to the EUTXO ledger, formally verified in Agda.

Ergo's research takes the "suspended computation" concept further. Chepurnoy and Saxena's **"Multi-stage Contracts in the UTXO Model"** (DPM/CBT 2019) explicitly demonstrates transaction trees where "each stage encodes data AND code to be carried to the next stage." Their companion paper **"Self-reproducing Coins as Universal Turing Machine"** (ESORICS 2018) proves Turing-completeness of UTXO systems by showing computation can proceed "between transactions"—the blockchain acts as a tape with UTXOs as suspended computation states.

| Platform | State Storage | Code Location | State Machine Model |
|----------|--------------|---------------|---------------------|
| Cardano EUTXO | Datum field on outputs | Validator scripts | Constraint Emitting Machines |
| Ergo | Box registers R0-R9 | ErgoScript guards | Transaction trees/chains |
| Nervos CKB | Cell data field | Lock/Type Scripts | Cell consumption/creation |

Nervos CKB's **Cell Model** provides the most general implementation—Cells are arbitrary state containers storing any bytes (state, code, JSON) with associated Lock Scripts (ownership) and Type Scripts (state transition rules). Zahnentferner's **"An Abstract Model of UTxO-based Cryptocurrencies with Scripts"** (IACR ePrint 2018/469) provides the theoretical foundation underlying all these approaches.

## Coordination scripts build on read-write set architectures

Transaction choreography and explicit read/write set declarations for parallelism have extensive prior art. Hyperledger Fabric's **execute-order-validate (EOV) architecture** (Androulaki et al., EuroSys 2018) pioneered explicit read-write sets: transactions are simulated at endorsers which produce read-write sets containing keys and version numbers, enabling parallel execution with version-based conflict detection.

**Block-STM** (Gelashvili et al., PPoPP 2023) represents the state-of-the-art for parallel execution engines, achieving **160k TPS on Aptos** with up to 17x improvement over sequential execution. It uses Software Transactional Memory principles with a key insight: preset transaction ordering becomes a performance blessing enabling deterministic conflict resolution without a priori read/write knowledge.

For UTXO-specific coordination, **Chainspace** (Al-Bassam et al., NDSS 2018) introduces the **S-BAC protocol** (Sharded Byzantine Atomic Commit)—transactions explicitly specify input/output objects, and shards coordinate atomically across multiple objects using explicit state machines (active → locked → inactive). This directly relates to coordination scripts managing multi-UTXO state transitions.

Cross-chain coordination protocols also provide relevant prior art. Zakhary et al.'s **"Atomic Commitment Across Blockchains"** (VLDB 2020) and Cai et al.'s **Avalon protocol** (IACR ePrint 2024/1084) demonstrate layered state commitments achieving "complete atomicity" with explicit authorization state machines coordinating transitions across multiple chains—patterns applicable to intra-chain multi-UTXO coordination.

## Algebraic effects remain implicit but functionally present

**No paper directly applies algebraic effect handlers to smart contracts**, making this potentially the most novel component of Starstream. However, effect-like patterns pervade functional blockchain languages.

**Scilla** (Sergey et al., OOPSLA 2019) comes closest, explicitly distinguishing between pure expressions, impure local state manipulations, and blockchain reflection (reading block number). It uses continuation-passing style and communicating automata, preventing reentrancy through structural constraints. The paper explicitly draws from "functional programming with effects."

Cardano's **Plutus** achieves similar goals differently: scripts are pure validators where external dependencies (oracles) are handled through transaction context. This mirrors algebraic effect handlers—contracts express requirements, and the transaction context "handles" them by providing implementations. **Marlowe** (Seijas & Thompson, ISoLA 2018), the financial DSL atop Plutus, makes oracle handling explicit through **observable values**—contracts request external data as explicit language constructs handled at execution time.

The gap in literature suggests **explicit algebraic effect handlers for smart contracts**—with custom effect types for oracles, payments, and state updates composed via handler-based semantics—would represent a genuinely novel contribution.

## IVC and folding schemes have mature theoretical foundations

Incrementally verifiable computation represents the most actively researched component. **Nova** (Kothapalli, Setty, Tzialla; CRYPTO 2022) introduces **folding schemes**—a primitive simpler than SNARKs that reduces checking two NP instances to checking one. Nova achieves the fastest prover with only ~10,000 gate recursion overhead, directly applicable to succinct blockchain state verification.

The Nova family has expanded rapidly:

- **SuperNova** (2022) enables non-uniform IVC for VMs with multiple instructions—crucial for zkVM implementations where proving costs scale with executed instruction type rather than universal circuits
- **HyperNova** (CRYPTO 2024) extends folding to Customizable Constraint Systems (CCS), generalizing R1CS, Plonkish, and AIR with "à la carte" prover costs
- **Mova** (2024) optimizes Nova by eliminating error term commitments, achieving **5-10x faster proving**

**Proof-Carrying Data from Accumulation Schemes** (Bünz, Chiesa, Mishra, Spooner; TCC 2020) formalizes accumulation as an alternative to recursive SNARKs—showing PCD achievable even from SNARKs without sublinear verifiers. This theoretical framework underlies most modern recursive proof systems.

For blockchain applications, **Mina Protocol** (formerly Coda) deployed the first production succinct blockchain using recursive zk-SNARKs in 2018—the entire chain compresses to ~22KB regardless of history. **Derecho** (Beal & Fisch, CCS 2024) demonstrates PCD for Ethereum privacy pools, propagating allowlist membership proofs through transaction graphs.

The paper **"Reducing Participation Costs via Incremental Verification for Ledger Systems"** (IACR ePrint 2020/1522) explicitly evaluates IVC for UTXO-based payment systems, showing orders of magnitude synchronization cost reduction for simplified Bitcoin models.

## Parallel execution through UTXO isolation has production deployments

Parallel smart contract execution through UTXO-style isolation has the most extensive industry deployment. Dickerson et al.'s **"Adding Concurrency to Smart Contracts"** (PODC 2017) established the theoretical foundation, adapting Software Transactional Memory for blockchain miners to discover serializable concurrent schedules encoded as deterministic fork-join programs.

Three production approaches dominate:

**Move's linear types** (Blackshear et al., Diem 2020) provide static safety guarantees—resources can never be copied or implicitly discarded, only moved between storage locations. Linear/affine types enable the compiler to prove non-interference, allowing safe parallel execution. Move powers both Sui and Aptos.

**Sui's object model** (Blackshear et al., CCS 2024) combines consensusless agreement with explicit object accesses declared in transaction metadata. This achieves **sub-second finality** (<0.5s) at 5,000 certificates/second by statically scheduling non-conflicting transactions for parallel execution. Objects are "long-lived but manipulated atomically through versioning"—a middle ground between pure UTXOs and accounts.

**Solana's Sealevel runtime** requires transactions to describe all states they will read/write, enabling non-overlapping transactions to execute concurrently across all CPU cores. **Fuel's FuelVM** uses strict UTXO-style state access lists to identify dependencies before execution, with stateless "predicates" for efficient parallel validation.

Garamvölgyi et al.'s empirical study (ICSE 2022) found Ethereum's achievable parallelism limited to ~4x with optimal scheduling due to ERC20 token bottlenecks—demonstrating why UTXO-style isolation or explicit access declarations are necessary for meaningful parallelism gains.

## The synthesis represents novel contribution space

While each individual component has substantial prior art, their specific integration as described in the Starstream Paradigm—particularly **coroutinized UTXOs with algebraic effect handlers coordinated through explicit choreography scripts while carrying recursively folded validity proofs**—appears to occupy novel territory.

Key research gaps where Starstream may offer new contributions:

- **Explicit algebraic effect handlers for smart contracts** with custom effect types and handler-based composition
- **IVC specifically for UTXO asset history compression** combining folding schemes with per-asset proof chains (rather than chain-wide state proofs like Mina)
- **Coordination scripts as first-class choreography primitives** with formal semantics connecting to algebraic effects for dependency expression

The most relevant foundational works for any prior art claims are: the EUTXO model paper (Chakravarty et al., FC 2020) for stateful UTXOs; Block-STM (PPoPP 2023) and S-BAC/Chainspace (NDSS 2018) for coordination; Scilla (OOPSLA 2019) for effect separation; Nova (CRYPTO 2022) and the PCD/accumulation framework (TCC 2020) for IVC; and Sui Lutris (CCS 2024) with Move for parallel execution via object/resource isolation.