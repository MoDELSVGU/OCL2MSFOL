import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import org.vgu.dm2schema.dm.DataModel;
import org.vgu.se.smt.dm.DM2MSFOL;
import org.vgu.se.smt.file.FileManager;
import org.vgu.se.smt.ocl.OCL2MSFOL;

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

public class Main {
    public static void main(String[] args) throws ParseException, Exception {
        FileManager fm = FileManager.getInstance();
        /*** 28th Oct Hoang: Change this to true to suppress invalid type ***/
        fm.setSafeMode(false);
        fm.init();
//        DataModel dm = setDataModelFromFile("resources\\vgu_dm.json");
        DataModel dm = setDataModelFromFile("resources\\dm_fol.json");

        DM2MSFOL.setDataModel(dm);
        DM2MSFOL.map(fm);
        OCL2MSFOL.setDataModel(dm);
        OCL2MSFOL.setExpression("Student.allInstances()->isEmpty()");
        OCL2MSFOL.map(fm);

//        
//        fm.checkSat();
        fm.close();

//        int counter = 1;
//        while (true) {
//            Scanner sc = new Scanner(System.in);
//            String key = sc.nextLine();
//            String value = sc.nextLine();
//            String[] inputs = value.split(" ");
//            Expression exp = null;
//            switch (key) {
//            case "b":
//                exp = new BooleanValue();
//                ((BooleanValue) exp).setValue(Boolean.valueOf(inputs[0]));
//                break;
//            case "i":
//                exp = new LongValue();
//                ((LongValue) exp).setValue(String.valueOf(inputs[0]));
//                break;
//            case "=":
//                exp = new EqualsTo();
//                ((EqualsTo) exp).setLeft(SQL2MSFOL.map(inputs[0]));
//                ((EqualsTo) exp).setRight(SQL2MSFOL.map(inputs[1]));
//                break;
//            case ">":
//                exp = new GreaterThan();
//                ((GreaterThan) exp).setLeft(SQL2MSFOL.map(inputs[0]));
//                ((GreaterThan) exp).setRight(SQL2MSFOL.map(inputs[1]));
//                break;
//            case "case":
//                exp = new CaseWhenThen();
//                ((CaseWhenThen) exp).setCaze(SQL2MSFOL.map(inputs[0]));
//                ((CaseWhenThen) exp).setWhen(SQL2MSFOL.map(inputs[1]));
//                ((CaseWhenThen) exp).setElze(SQL2MSFOL.map(inputs[2]));
//                break;
//            case "not":
//                exp = new Not();
//                ((Not) exp).setExp(SQL2MSFOL.map(inputs[0]));
//                break;
//            case "isnull":
//                exp = new IsNull();
//                ((IsNull) exp).setExp(SQL2MSFOL.map(inputs[0]));
//                break;
//            case "true":
//                System.out.println(SQL2MSFOL.map(inputs[0]).toTrue());
//                return;
//            case "false":
//                System.out.println(SQL2MSFOL.map(inputs[0]).toFalse());
//                return;
//            case "null":
//                System.out.println(SQL2MSFOL.map(inputs[0]).toNull());
//                return;
//            }
//            SQL2MSFOL.add(key.concat(String.valueOf(counter++)), exp);
//            SQL2MSFOL.print();
//        }

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
