### Running Promela Models with iSpin
1. Open iSpin
2. Open file in Edit/View Tab
3. Click on Verification tab
4. Click Safety under Safety subsection
5. Click on "Use claim" under Never Claims subsection
6. Enter "inv" into "claim name (opt)" text box
7. Click Run
8. Return to Step 2 to test other files

### Running Empirical Java Tests
The implementation of the concurrent set is found under `ConcurrentSet.java`, whilst the naive set for performance comparison is found under `NaiveSet.java`.
Our empirical java tests are found under `Test.java`. 
To run our empirical tests, build the project and run the `Test.java` binary.
