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

package org.vgu.se.smt.sql;

public class BooleanValue implements Expression {
    private Boolean value;

    public Boolean getValue() {
        return value;
    }

    public void setValue(Boolean value) {
        this.value = value;
    }

    @Override
    public String toTrue() {
        return String.valueOf(value);
    }

    @Override
    public String toFalse() {
        return String.valueOf(!value);
    }

    @Override
    public String toNull() {
        return "false";
    }

    @Override
    public String toExec() {
        // TODO Auto-generated method stub
        return null;
    }
    
    @Override
    public String toString() {
        return String.valueOf(value);
    }
}
