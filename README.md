# Advanced Formal Methods: Final Project

Modelling Blockchain consensus (Proof-of-Work) with TLA+

Project developed for Advanced Formal Methods course (17624) in Fall 2022 (Mini 2), under the guidance of Eunsuk Kang and David Garlan

- - -

## Running instructions

### TLA+ Toolbox on Windows

- Open BlockchainFinal as the root-level module
- This step is only needed if after step #1, the helper modules were NOT imported. Add Helper Modules: SimpleInput.tla, FiniteSetsExt.tla and ConsensusLength.tla
  - Click File -> Open Module -> Add TLA+ Module and select the modules
- Create a model with the spec and properties as shown in the BlockchainFinal.cfg file. Please note there are two properties to be added in the UI.
- Run model to verify that no temporal properties were violated
- To run the earlier version refernced in the PPT and write up which has a slightly different implementation, create a new root module and repeat from step 1 selecting Blockchain.tla as the root-level module and Blockchain.cfg as the model reference.

### TLA+ Toolbox on MacOS

- Open BlockchainFinal as the root-level module. You will be presented with a dialog that states that you will be "replacing" the BlockchainFinal file. Please ignore it. The TLA+ UI does not have an open option. The TLA+ toolbox handles the replace as an open action.
- This step is only needed if after step #1, the helper modules were NOT imported. Add Helper Modules: SimpleInput.tla, FiniteSetsExt.tla and ConsensusLength.tla
  - Click File -> Open Module -> Add TLA+ Module and select the modules
- Create a model with the spec and properties as shown in the BlockchainFinal.cfg file. Please note there are two properties to be added in the UI.
- Run model to verify that no temporal properties were violated
- To run the earlier version refernced in the PPT and write up which has a slightly different implementation, create a new root module and repeat from step 1 selecting Blockchain.tla as the root-level module and Blockchain.cfg as the model reference.

### VSCode

- Blockchain and BlockchainFinal should be directly runnable from the VSCode extension
- Config files are provided for both (with the same name) and can be customized

- - -

## Contributors:

- Dennis Peter George
- Hemant Hari Kumar
