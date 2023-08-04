/*
 * SPDX-FileCopyrightText: 2021-2023 The Refinery Authors <https://refinery.tools/>
 *
 * SPDX-License-Identifier: EPL-2.0
 */

plugins {
	id("tools.refinery.gradle.java-library")
}

dependencies {
	api(project(":refinery-store-query"))
	api(project(":refinery-store-query-viatra"))
	api(project(":refinery-store-reasoning"))
	api(project(":refinery-visualization"))
}
