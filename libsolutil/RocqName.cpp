/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERMERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsolutil/RocqName.h>

#include <cctype>
#include <set>

using namespace solidity;

std::string util::rocqModuleName(std::string _name)
{
	for (char& character: _name)
	{
		unsigned char const byte = static_cast<unsigned char>(character);
		if (!std::isalnum(byte) && character != '_')
			character = '_';
	}

	static std::set<std::string> const reservedNames{
		"as", "at", "cofix", "else", "end", "exists", "exists2", "fix", "for",
		"forall", "fun", "if", "in", "let", "match", "mod", "Prop", "return",
		"Set", "then", "Type", "using", "where", "with"
	};

	if (_name.empty() || std::isdigit(static_cast<unsigned char>(_name.front())) || reservedNames.count(_name))
		_name = "Rocq_" + _name;

	return _name;
}
