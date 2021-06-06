import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import org.vgu.dm2schema.dm.Association;
import org.vgu.dm2schema.dm.Attribute;
import org.vgu.dm2schema.dm.DataModel;
import org.vgu.dm2schema.dm.DmUtils;
import org.vgu.dm2schema.dm.Entity;
import org.vgu.se.smt.dm.DM2MSFOL;
import org.vgu.se.smt.file.FileManager;
import org.vgu.se.smt.logicvalue.LogicValue;
import org.vgu.se.smt.ocl.OCL2MSFOL;
import org.vgu.sqlsi.sec.Auth;
import org.vgu.sqlsi.sec.SecPolicyModel;
import org.vgu.sqlsi.sec.SecRuleModel;
import org.vgu.sqlsi.sec.SecUnitRule;
import org.vgu.sqlsi.sec.SecurityMode;
import org.vgu.sqlsi.sql.func.SQLSIAuthFunction;
import org.vgu.sqlsi.utils.FunctionUtils;
import org.vgu.sqlsi.utils.RuleUtils;

/**************************************************************************
 * Copyright 2020 Vietnamese-German-University
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
 * @author: ngpbh
 ***************************************************************************/

public class Runner {
    public static void main(String[] args) throws ParseException, Exception {
        FileManager fm = FileManager.getInstance();
        fm.setSafeMode(false);
        fm.init();
        
        DataModel dm = setDataModelFromFile("resources\\company.json");
        SecPolicyModel sm = setSecurityModelFromFile("resources\\policy.json");
        DM2MSFOL.setDataModel(dm);
        DM2MSFOL.map2msfol(fm);
        
        OCL2MSFOL.setDataModel(dm);
        
        List<String> invariants = new ArrayList<String>();
        for(String inv : invariants) {
        	fm.commentln(inv);
            OCL2MSFOL.setExpression(inv);
            OCL2MSFOL.setLvalue(LogicValue.TRUE);
        	OCL2MSFOL.map2msfol(fm);
        }
        
        fm.commentln("Ad-hoc Contextual Model");
        OCL2MSFOL.putAdhocContextualSet("kcaller", "Employee");
        OCL2MSFOL.putAdhocContextualSet("kself", "Employee");
        
        boolean isAttribute = true;
        
        String role = "Employee";
        
        List<String> callerProperties = new ArrayList<String>();
        for(String prop : callerProperties) {
        	fm.commentln(prop);
            OCL2MSFOL.setExpression(prop);
            OCL2MSFOL.setLvalue(LogicValue.TRUE);
        	OCL2MSFOL.map2msfol(fm);
        }

        if(isAttribute) {
        	String sClass = "Employee";
            String sAattribute = "email";
            List<String> selfProperties = new ArrayList<String>();
            for(String prop : selfProperties) {
            	fm.commentln(prop);
                OCL2MSFOL.setExpression(prop);
                OCL2MSFOL.setLvalue(LogicValue.TRUE);
            	OCL2MSFOL.map2msfol(fm);
            }
        	String authOcl = extracted(dm, sm, sClass, sAattribute, role);
        	fm.commentln(authOcl);
            OCL2MSFOL.setExpression(authOcl);
            OCL2MSFOL.setLvalue(LogicValue.TRUE);
            OCL2MSFOL.map2msfol(fm);
        } else {
        	String sAssociation = "Supervision";
        	List<String> aseLProperties = new ArrayList<String>();
            for(String prop : aseLProperties) {
            	fm.commentln(prop);
                OCL2MSFOL.setExpression(prop);
                OCL2MSFOL.setLvalue(LogicValue.TRUE);
            	OCL2MSFOL.map2msfol(fm);
            }
            List<String> aseRProperties = new ArrayList<String>();
            for(String prop : aseRProperties) {
            	fm.commentln(prop);
                OCL2MSFOL.setExpression(prop);
                OCL2MSFOL.setLvalue(LogicValue.TRUE);
            	OCL2MSFOL.map2msfol(fm);
            }
        	String authOcl = extracted(dm, sm, role, sAssociation);
    		fm.commentln(authOcl);
            OCL2MSFOL.setExpression(authOcl);
            OCL2MSFOL.setLvalue(LogicValue.TRUE);
            OCL2MSFOL.map2msfol(fm);
        }
        
        fm.checkSat();
        fm.close();
    }

	private static String extracted(DataModel dm, SecPolicyModel sm, String role, String sAssociation) {
		Association association = getAssociation(dm,sAssociation);
		List<SecUnitRule> rules = RuleUtils.getAllUnitRules(sm);
		HashMap<String, List<SecUnitRule>> indexRules = FunctionUtils.filterAndIndexRules(
				"READ", association, rules);
		List<SecUnitRule> ruleRoleBased = indexRules.get(role);
		List<String> authChecks = ruleRoleBased.stream().map(SecUnitRule::getAuths)
		        .flatMap(auths -> auths.stream().map(Auth::getOcl))
		        .collect(Collectors.toList());
		String authOcl = null;
		if(authChecks!= null && !authChecks.isEmpty()) {
			if (authChecks.size() == 1) {
				authOcl = authChecks.get(0);
			} else {
				authOcl = authChecks.get(0);
				for(int i = 1; i < authChecks.size(); i++) {
					authOcl = authOcl.concat(" or ").concat(authChecks.get(i));
				}
			}
		}
		return authOcl;
	}

	private static Association getAssociation(DataModel dm, String sAssociation) {
		Set<Association> associations = dm.getAssociations();

        for (Association as : associations) {
            if (as.getName().equals(sAssociation)) {
                return as;
            }
        }
        return null;
	}

	private static String extracted(DataModel dm, SecPolicyModel sm, String sClass, String sAattribute, String role) {
		Entity entity = dm.getEntities().get(sClass);
		Attribute attribute = getAttribute(dm, sClass, sAattribute);
		List<SecUnitRule> rules = RuleUtils.getAllUnitRules(sm);
		HashMap<String, List<SecUnitRule>> indexRules = FunctionUtils.filterAndIndexRules(
				"READ", entity, attribute, rules);
		List<SecUnitRule> ruleRoleBased = indexRules.get(role);
		List<String> authChecks = ruleRoleBased.stream().map(SecUnitRule::getAuths)
		        .flatMap(auths -> auths.stream().map(Auth::getOcl))
		        .collect(Collectors.toList());
		String authOcl = null;
		if(authChecks!= null && !authChecks.isEmpty()) {
			if (authChecks.size() == 1) {
				authOcl = authChecks.get(0);
			} else {
				authOcl = authChecks.get(0);
				for(int i = 1; i < authChecks.size(); i++) {
					authOcl = authOcl.concat(" or ").concat(authChecks.get(i));
				}
			}
		}
		return authOcl;
	}

	private static SecPolicyModel setSecurityModelFromFile(String securityModelURI) throws FileNotFoundException, IOException, ParseException {
    	File policyFile = new File(securityModelURI);
		JSONArray secureUMLJSONArray = (JSONArray) new JSONParser().parse(new FileReader(policyFile));
		SecPolicyModel secureUML = new SecPolicyModel(secureUMLJSONArray);
		return secureUML;
	}

	private static Attribute getAttribute(DataModel dm,
            String className, String attName) {
        Entity entity = dm.getEntities().get(className);

        Set<Attribute> atts = entity.getAttributes();

        for (Attribute att : atts) {
            if (att.getName().equals(attName)) {
                return att;
            }
        }

        return null;
    }

    @SuppressWarnings("unused")
    private static List<String> readFromFile(String filePath) throws IOException {
        File file = new File(filePath);
        FileReader fileReader = new FileReader(file);
        BufferedReader bufferReader = new BufferedReader(fileReader);  //creates a buffering character input stream  
        String line;
        List<String> lines = new ArrayList<String>();
        
        while((line = bufferReader.readLine())!=null) {  
            lines.add(line); 
        }  
        fileReader.close(); 
        return lines;
    }

    private static DataModel setDataModelFromFile(String filePath)
        throws FileNotFoundException, IOException, ParseException, Exception {
        return transformToDataModel(filePath);
    }

    private static DataModel transformToDataModel(String dataModelURI)
        throws IOException, ParseException, FileNotFoundException, Exception {
        File dataModelFile = new File(dataModelURI);
        JSONArray dataModelJSONArray = (JSONArray) new JSONParser()
            .parse(new FileReader(dataModelFile));
        DataModel context = new DataModel(dataModelJSONArray);
        return context;
    }
}
