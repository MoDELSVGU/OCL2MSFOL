/**************************************************************************
Copyright 2020 ngpbh
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

package org.vgu.se.smt.ocl;

import java.util.List;

import org.vgu.dm2schema.dm.DataModel;

import com.vgu.se.jocl.expressions.Variable;
import com.vgu.se.jocl.visit.ParserVisitor;

public abstract class OCL2MSFOLVisitor implements ParserVisitor {
    protected DataModel dm;
    protected O2F_NullVisitor nullVisitor;
    protected O2F_TrueVisitor trueVisitor;
    protected O2F_FalseVisitor falseVisitor;
    protected O2F_InvalidVisitor invalVisitor;
    protected O2F_EvalVisitor evalVisitor;

    public void setDataModel(DataModel dm) {
        this.dm = dm;
    }
    
    public DataModel getDataModel() {
        return this.dm;
    }

    private String fol;

    public String getFOLFormulae() {
        return this.fol;
    }
    
    public void setFOLFormulae(String fol) {
        this.fol = fol;
    }

    protected String app(String folFormulae, List<Variable> fvExp, String var) {
        String output = folFormulae;
        for (Variable v : fvExp) {
            output = output.concat("_").concat(v.getName());
        }
        output = output.concat("_").concat(var);
        return output;
    }
    
    protected String nullOf(String type) {
        return "null".concat(type.substring(0, 1).toUpperCase()).concat(type.substring(1));
    }
    
    protected String invalidOf(String type) {
        return "invalid".concat(type.substring(0, 1).toUpperCase()).concat(type.substring(1));
    }
}
