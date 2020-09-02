import java.io.File;
import java.io.FileReader;

import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.vgu.dm2schema.dm.DataModel;

/**************************************************************************
Copyright 2020 Vietnamese-German-University

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

@author: ngpbh
***************************************************************************/

public class Main {
    public static void main (String[] args) throws Exception {
        File dataModelFile = new File("resources/vgu_dm.json");
        JSONArray dataModelJSONArray = (JSONArray) new JSONParser()
            .parse(new FileReader(dataModelFile));
        DataModel dataModel = new DataModel(dataModelJSONArray);
        
        
        Configuration config = Configuration.fromCmdLineArguments(args);
        LogManager logger = BasicLogManager.create(config);
        ShutdownManager shutdown = ShutdownManager.create();

        // SolverContext is a class wrapping a solver context.
        // Solver can be selected either using an argument or a configuration option
        // inside `config`.
        SolverContext context = SolverContextFactory.createSolverContext(
            config, logger, shutdown.getNotifier(), Solvers.CVC4);
        
        O2FData.map(dataModel, context);
        
        // Assume we have a SolverContext instance.
        FormulaManager fmgr = context.getFormulaManager();

        BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
        IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
        
        IntegerFormula a = imgr.makeVariable("a"),
                       b = imgr.makeVariable("b"),
                       c = imgr.makeVariable("c");
        BooleanFormula constraint = bmgr.or(
            imgr.equal(
                imgr.add(a, b), c
            ),
            imgr.equal(
                imgr.add(a, c), imgr.multiply(imgr.makeNumber(2), b)
            )
        );
        try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
            prover.addConstraint(constraint);
            boolean isUnsat = prover.isUnsat();
            if (!isUnsat) {
              Model model = prover.getModel();
              System.out.println(model);
            }
          }
    }
}
