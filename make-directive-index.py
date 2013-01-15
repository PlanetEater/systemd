#  -*- Mode: python; coding: utf-8; indent-tabs-mode: nil -*- */
#
#  This file is part of systemd.
#
#  Copyright 2012 Zbigniew Jędrzejewski-Szmek
#
#  systemd is free software; you can redistribute it and/or modify it
#  under the terms of the GNU Lesser General Public License as published by
#  the Free Software Foundation; either version 2.1 of the License, or
#  (at your option) any later version.
#
#  systemd is distributed in the hope that it will be useful, but
#  WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
#  Lesser General Public License for more details.
#
#  You should have received a copy of the GNU Lesser General Public License
#  along with systemd; If not, see <http://www.gnu.org/licenses/>.

import sys
import collections
import xml.etree.ElementTree as tree

TEMPLATE = '''\
<refentry id="systemd.directives">

        <refentryinfo>
                <title>systemd.directives</title>
                <productname>systemd</productname>

                <authorgroup>
                        <author>
                                <contrib>Developer</contrib>
                                <firstname>Zbigniew</firstname>
                                <surname>Jędrzejewski-Szmek</surname>
                                <email>zbyszek@in.waw.pl</email>
                        </author>
                </authorgroup>
        </refentryinfo>

        <refmeta>
                <refentrytitle>systemd.directives</refentrytitle>
                <manvolnum>7</manvolnum>
        </refmeta>

        <refnamediv>
                <refname>systemd.directives</refname>
                <refpurpose>Index of configuration directives</refpurpose>
        </refnamediv>

        <refsect1>
                <title>Unit directives</title>

                <para>Directives for configuring units, used in unit
                files.</para>

                <variablelist id='unit-directives' />
        </refsect1>

        <refsect1>
                <title>System manager directives</title>

                <para>Directives for configuring the behaviour of the
                systemd process.</para>

                <variablelist id='systemd-directives' />
        </refsect1>

        <refsect1>
                <title>Options on the kernel command line</title>

                <para>Kernel boot options for configuring the behaviour of the
                systemd process.</para>

                <variablelist id='kernel-commandline-directives' />
        </refsect1>

        <refsect1>
                <title>Environment variables</title>

                <para>Environment variables understood by the systemd process.</para>

                <variablelist id='environment-variables' />
        </refsect1>

        <refsect1>
                <title>UDEV directives</title>

                <para>Directives for configuring systemd units through the
                udev database.</para>

                <variablelist id='udev-directives' />
        </refsect1>

        <refsect1>
                <title>Journal directives</title>

                <para>Directives for configuring the behaviour of the
                journald process.</para>

                <variablelist id='journal-directives' />
        </refsect1>

        <refsect1>
                <title>bootchart.conf directives</title>

                <para>Directives for configuring the behaviour of the
                systemd-bootchart process.</para>

                <variablelist id='bootchart-directives' />
        </refsect1>

        <refsect1>
                <title>Colophon</title>
                <para id='colophon' />
        </refsect1>
</refentry>
'''

COLOPHON = '''\
This index contains {count} entries in {sections} sections,
referring to {pages} individual manual pages.
'''

def _extract_directives(directive_groups, page):
    t = tree.parse(page)
    section = t.find('./refmeta/manvolnum').text
    pagename = t.find('./refmeta/refentrytitle').text
    for variablelist in t.iterfind('.//variablelist'):
        klass = variablelist.attrib.get('class') or 'unit-directives'
        stor = directive_groups[klass]
        for varname in variablelist.iterfind('./varlistentry/term/varname'):
            text = ''.join(varname.text.partition('=')[:2])
            stor[text].append((pagename, section))

def _make_section(template, name, directives):
    varlist = template.find(".//*[@id='{}']".format(name))
    for varname, manpages in sorted(directives.items()):
        entry = tree.SubElement(varlist, 'varlistentry')
        a = tree.SubElement(tree.SubElement(entry, 'term'), 'varname')
        a.text = varname
        para = tree.SubElement(tree.SubElement(entry, 'listitem'), 'para')

        b = None
        for manpage, manvolume in sorted(manpages):
                if b is not None:
                        b.tail = ', '
                b = tree.SubElement(para, 'citerefentry')
                c = tree.SubElement(b, 'refentrytitle')
                c.text = manpage
                d = tree.SubElement(b, 'manvolnum')
                d.text = manvolume
        entry.tail = '\n\n'

def _make_colophon(template, groups):
    count = 0
    pages = set()
    for group in groups:
        count += len(group)
        for pagelist in group.values():
            pages |= set(pagelist)

    para = template.find(".//para[@id='colophon']")
    para.text = COLOPHON.format(count=count,
                                sections=len(groups),
                                pages=len(pages))

def _make_page(template, directive_groups):
    """Create an XML tree from directive_groups.

    directive_groups = {
       'class': {'variable': [('manpage', 'manvolume'), ...],
                 'variable2': ...},
       ...
    }
    """
    for name, directives in directive_groups.items():
            _make_section(template, name, directives)

    _make_colophon(template, directive_groups.values())

    return template

def make_page(xml_files):
    "Extract directives from xml_files and return XML index tree."
    template = tree.fromstring(TEMPLATE)
    names = [vl.get('id') for vl in template.iterfind('.//variablelist')]
    directive_groups = {name:collections.defaultdict(list)
                        for name in names}
    for page in xml_files:
        _extract_directives(directive_groups, page)

    return _make_page(template, directive_groups)

if __name__ == '__main__':
    tree.dump(make_page(sys.argv[1:]))
