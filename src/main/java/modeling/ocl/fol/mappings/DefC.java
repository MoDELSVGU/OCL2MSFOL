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

package modeling.ocl.fol.mappings;

public class DefC {
	private String nameDefinition;
	private String nameApplied;
	private String assertion;

	public String getNameDefinition() {
		return nameDefinition;
	}

	public void setNameDefinition(String nameDefinition) {
		this.nameDefinition = nameDefinition;
	}

	public String getNameApplied() {
		return nameApplied;
	}

	public void setNameApplied(String nameApplied) {
		this.nameApplied = nameApplied;
	}

	public String getAssertion() {
		return assertion;
	}

	public void setAssertion(String assertion) {
		this.assertion = assertion;
	}
}
