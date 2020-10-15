# A Formal Model of the Double-Ratchet Algorithm with Clone Detection

This repository accompanies the paper [Clone Detection in Secure Messaging: Improving Post-Compromise Security in Practice](https://people.cispa.io/cas.cremers/downloads/papers/CFKN2020-messaging_cloning.pdf) by Cas Cremers, Jaiden Fairoze, Benjamin Kiesl, and Aurora Naska; it contains a formal model of a modified version of [Signal's double-ratchet algorithm](https://signal.org/docs/specifications/doubleratchet/). This version of the double ratchet allows a user to detect when their communication partner was cloned. The model is created for the theorem prover [Tamarin](https://tamarin-prover.github.io/) and is discussed in a CCS submission that is currently under review.

## Prerequisites

To produce our formal model and the corresponding proofs, we used the [Tamarin prover](https://tamarin-prover.github.io/) version 1.4.1. Installation instructions for Tamarin can be found [here](https://tamarin-prover.github.io/manual/book/002_installation.html). You need Tamarin to inspect the model, run proofs, and verify existing proofs. Note that Tamarin runs on Linux and Mac, but not on Windows. If you plan to use or edit the model, you also need the [GNU M4 macro preprocessor](https://www.gnu.org/software/m4/).

## Files of the Formal Model

The main file, containing the formal model of the double ratchet together with all lemmas, is [model/double_ratchet.m4](model/double_ratchet.m4). This file needs to be preprocessed with the [GNU M4 macro preprocessor](https://www.gnu.org/software/m4/) to turn it into valid input for Tamarin. This can be done with the following shell command: 

`m4 double_ratchet.m4 > double_ratchet.spthy`

If you don't want to use M4 and are only interested in the resulting Tamarin file, then the file [model/double_ratchet.spthy](model/double_ratchet.spthy) is enough. 


## Overview of the Model

The model file [double_ratchet.m4](model/double_ratchet.m4) consists of the following parts (in the same order as presented here):

* Several definitions of constants/macros as well as definitions of function symbols.

* Restrictions (starting at line 44) stating (1) that a pair of users can have only one conversation/association, (2) that users cannot associate with themselves, (3) that a pair of users cannot perform two or more initializations in parallel, (4) that messages from one sender thread must arrive in the order in which they were sent, (5) checks for equality and inequality (used, e.g., for modeling the verification of message authentication codes), and (6) semantics of the clone-detection mechanism.

* The Send and Receive rules modeling the communication channels between users (starting at line 92).

* The initialization procedure for a communication session (starting at line 104).

* The rules for the actual messaging mechanism via the double ratchet, including the evolution of the root key, symmetric chain keys, and message keys (as defined by the double-ratchet algorithm) as well as the evolution of the message numbers and the computation of MACs that are part of our clone-detection mechanism (starting at line 223). These rules also model single-state loss.

* A rule for total-state loss (starting at line 454).

* A rule that allows the attacker to compromise a user's state by cloning it (starting at line 483).

The rest of the file then contains all lemmas (the first lemma is just a sanity lemma that is not related to the other proofs). The final lemma (*sound_clone_detection* at line 787) is the main statement, saying that the clone-detection mechanism is sound.

## Proof Files

The proofs of all lemmas are contained in the folder [proofs](proofs). Each file in the folder is named after the lemma it proves, with the suffix '.spthy'. For example, the proof of lemma 'sound_clone_detection' is in the file [proofs/sound_clone_detection.spthy](proofs/sound_clone_detection.spthy). 

To validate a proof and to inspect it in the Tamarin GUI, just start Tamarin in *interactive mode* and then open the corresponding file (we recommend to start interactive mode in a folder different from [proofs](proofs) because otherwise Tamarin runs on all the files in this folder, which could take very long):

`tamarin-prover --interactive [start_folder_for_interactive_mode]`

Above, replace `[start_folder_for_interactive_mode]` by the folder from which you want to run Tamarin.
