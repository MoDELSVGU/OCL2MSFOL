/**************************************************************************
 * Copyright 2020 Vietnamese-German-University -- 2023 ETH Zurich
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 * 
 * @author: hoangnguyen (hoang.nguyen@inf.ethz.ch)
 ***************************************************************************/

package modeling.ocl.fol.config;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.json.simple.parser.ParseException;

import modeling.data.entities.DataModel;
import modeling.data.mappings.DMParser;
import modeling.datamodel.fol.DM2MSFOL;
import modeling.ocl.fol.mappings.OCL2MSFOL;
import modeling.ocl.fol.utils.FileManager;

public class Runner {
	public static void main(String[] args) throws FileNotFoundException, IOException, ParseException, Exception {

		String outputFilePath = "theory.smt2";
		String inputFilePath = null;
		List<Context> contexts = new ArrayList<Context>();
		List<String> invariants = new ArrayList<String>();
		String ocl = null;

		for (int i = 0; i < args.length; i++) {
			if ("-out".equalsIgnoreCase(args[i])) {
				outputFilePath = args[++i];
			} else if ("-in".equalsIgnoreCase(args[i])) {
				inputFilePath = args[++i];
			} else if ("-ctx".equalsIgnoreCase(args[i])) {
				while (!args[i + 1].contains("-")) {
					String[] s = args[i + 1].split(":");
					Context context = new Context(s[0], s[1]);
					contexts.add(context);
					i++;
				}
			} else if ("-inv".equalsIgnoreCase(args[i])) {
				while (!args[i + 1].contains("-")) {
					invariants.add(args[i + 1]);
					i++;
				}
			} else if ("-ocl".equalsIgnoreCase(args[i])) {
				ocl = args[i];
			}
		}

		if (inputFilePath == null) {
			throw new Exception("Missing input file path!");
		}

		if (ocl == null) {
			throw new Exception("Missing OCL expression!");
		}

		FileManager fm = FileManager.getInstance();
		fm.setSafeMode(false);
		fm.open(outputFilePath);
		fm.init();

		DataModel dm = DMParser.parse(inputFilePath);
		DM2MSFOL.setDataModel(dm);
		DM2MSFOL.map2msfol(fm);

		OCL2MSFOL.setDataModel(dm);

		for (Context ctx : contexts) {
			OCL2MSFOL.putAdhocContextualSet(ctx.getVar(), ctx.getType());
		}

		OCL2MSFOL.mapContext(fm);

		for (String invariant : invariants) {
			fm.commentln(invariant);
			OCL2MSFOL.setExpression(invariant);
			OCL2MSFOL.setLvalue(LogicValue.TRUE);
			OCL2MSFOL.map2msfol(fm, true);
		}

		OCL2MSFOL.setExpression(ocl);
		OCL2MSFOL.setLvalue(LogicValue.TRUE);
		OCL2MSFOL.map2msfol(fm, false);

		fm.close();
	}
}
